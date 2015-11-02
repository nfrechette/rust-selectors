/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

extern crate time as stdtime;

use parser::{CompoundSelector, Combinator, SimpleSelector, LocalName};
use matching::{self, DebugStats};
use tree::Element;
use bloom::BloomFilter;

// Our alphabet is:
//      parent matched
//      sibling matched
//      parent not matched
//      sibling not matched
//      end of stream
// Our input to test is the element tree starting at E. It starts with E,
// followed by all later siblings, followed by their parent, all its later
// siblings, etc. until the end of the stream.
// To convert our input into our alphabet, we apply the match function.
// Our initial state is a the first compound selector (left most).
// Our success state is a dummy state.
// Our fatal failure state is a dummy state.
// All other intermediary states are the compound selectors.
// There is thus 2 + num compound selector states.
// Our transition list is as follow:
// If our current state is the success state, we are done.
// If our current state is the fatal failure state, we are done.
// For all combinator states, if the last state matches, we go to success.
//
//
// If our current state is a child combinator (>)
//      parent matched -> next compound selector
//                  if no next selector, success
//
//      parent not matched -> prev compound selector
//                  skip prev child selector (>)
//                  skip prev next sibling selector (+)
//                  skip prev later sibling selector (~)
//                  if no prev selector, failure
//
//      sibling matched -> ..
//      sibling not matched -> no transition
//
//      end of stream -> failure state
//
//
// If our current state is a descendant combinator ('space')
//      parent matched -> next compound selector
//                  if no next selector, success
//
//      parent not matched -> ..
//      sibling matched -> ..
//      sibling not matched -> no transition
//
//      end of stream -> failure state
//
//
// If our current state is a next sibling combinator (+)
//      sibling matched -> next compound selector
//                  if no next selector, success
//
//      sibling not matched -> prev compound selector
//                  skip prev child selector (>)
//                  if a prev selector is child selector (>)
//                      skip prev later sibling selector (~)
//                  skip prev next sibling selector (+)
//                  if no prev selector, failure
//
//      parent matched -> ..
//      parent not matched -> ..
//      end of stream -> prev compound selector
//                  skip prev child selector (>)
//                  if a prev selector is child selector (>)
//                      skip prev later sibling selector (~)
//                  skip prev next sibling selector (+)
//                  if no prev selector, failure
//
//
// If our current state is a later sibling combinator (~)
//      sibling matched -> next compound selector
//                  if no next selector, success
//
//      sibling not matched -> no transition
//
//      parent matched -> ..
//      parent not matched -> ..
//      end of stream -> prev compound selector
//                  skip prev child selector (>)
//                  if a prev selector is child selector (>)
//                      skip prev later sibling selector (~)
//                  skip prev next sibling selector (+)
//                  if no prev selector, failure

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
pub enum State {
    Matched,
    Failed,
    Leaf,
    Child,
    Descendant,
    NextSibling,
    LaterSibling,
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
pub enum Symbol {
    Matched,
    NotMatched,
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum Direction {
    Parent,
    Sibling,
}

#[derive(PartialEq, Clone, Debug)]
pub struct StateInfo {
    state: State,
    direction: Direction,       // Which direction we iterate
    backtrack_distance: usize,  // How far to backtrack on failure
    first_selector_idx: usize,
    num_selectors: usize,
}

#[derive(PartialEq, Clone, Debug)]
pub struct SelectorNFA {
    pub state_list: Vec<StateInfo>,
    pub selector_list: Vec<SimpleSelector>,
}

fn get_direction(state: State) -> Direction {
    match state {
        State::Child |
        State::Descendant => Direction::Parent,
        _ => Direction::Sibling,
    }
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum BacktrackTarget {
    ClosestLaterSibling,
    ClosestDescendant,
}

fn get_backtrack_distance(state: State,
                          state_list: &Vec<StateInfo>)
                          -> usize {
    // We should always have at least our 2 artificial states
    if state_list.len() <= 2 { panic!(); }

    // Backtracking works by going back up 1 level on the evaluation stack
    // When a state fails a match for a node, we need to backtrack to
    // try either a different node for the same state (or a previous state
    // further up)
    // Thus, states that can skip nodes when a match fails (descendant, later
    // sibling) backtrack by 1 to try the next node and other states
    // need to backtrack by 2+ to try a previous state on a new node.

    let mut target = match state {
        // First two states are special artificial states
        State::Matched |
        State::Failed => panic!(),
        // If our leaf fails, we backtrack to the failed state
        State::Leaf => return 1,
        // If child fails, we backtrack looking for a previous descendant state
        State::Child => BacktrackTarget::ClosestDescendant,
        // If descendant fails, we backtrack once to try the next parent
        State::Descendant => return 1,
        // If next sibling fails, we backtrack looking for a previous later
        // sibling state
        State::NextSibling => BacktrackTarget::ClosestLaterSibling,
        // If later sibling fails, we backtrack once to try the next sibling
        State::LaterSibling => return 1,
    };

    // We need to try a previous state, thus at least twice
    let mut distance = 2;

    for info in state_list[2 .. state_list.len()].iter().rev() {
        match (target, info.state) {
            // If we meet a child node, we upgrade our search to the closest
            // descendant
            (_, State::Child) => {
                target = BacktrackTarget::ClosestDescendant;
            },
            // Keep whatever search target we had
            (_, State::NextSibling) => {}
            // Keep our closest descendant search target
            (BacktrackTarget::ClosestDescendant, State::LaterSibling) => {}
            // We hit our target state, stop
            _ => break,
        }

        distance += 1;
    }

    return distance;
}

fn get_states_internal(selector: &CompoundSelector,
                       state_list: &mut Vec<StateInfo>,
                       selector_list: &mut Vec<SimpleSelector>) {

    let (state, ref selectors) = match selector.next {
        None => return,
        Some((ref next_selector, Combinator::Child))
            => (State::Child, &next_selector.simple_selectors),
        Some((ref next_selector, Combinator::Descendant))
            => (State::Descendant, &next_selector.simple_selectors),
        Some((ref next_selector, Combinator::NextSibling))
            => (State::NextSibling, &next_selector.simple_selectors),
        Some((ref next_selector, Combinator::LaterSibling))
            => (State::LaterSibling, &next_selector.simple_selectors),
    };

    let first_idx = selector_list.len();
    selector_list.extend(selectors.iter().cloned());

    let distance = get_backtrack_distance(state, state_list);

    let info = StateInfo {
        state: state,
        direction: get_direction(state),
        backtrack_distance: distance,
        first_selector_idx: first_idx,
        num_selectors: selectors.len(),
    };

    state_list.push(info);

    match selector.next {
        None => return,
        Some((ref next, _)) => get_states_internal(&**next, state_list,
                                                   selector_list),
    };
}

fn get_states(selector: &CompoundSelector)
              -> (Vec<StateInfo>, Vec<SimpleSelector>) {
    let mut state_list = vec!();
    let mut selector_list = vec!();

    selector_list.extend(selector.simple_selectors.iter().cloned());

    state_list.push(StateInfo {
        state: State::Matched,
        direction: Direction::Parent,
        backtrack_distance: !0,
        first_selector_idx: !0,
        num_selectors: !0,
    });
    state_list.push(StateInfo {
        state: State::Failed,
        direction: Direction::Parent,
        backtrack_distance: !0,
        first_selector_idx: !0,
        num_selectors: !0,
    });
    state_list.push(StateInfo {
        state: State::Leaf,
        direction: Direction::Parent,
        backtrack_distance: 1,
        first_selector_idx: 0,
        num_selectors: selector.simple_selectors.len(),
    });

    get_states_internal(selector, &mut state_list, &mut selector_list);

    return (state_list, selector_list);
}

pub fn to_string(nfa: &SelectorNFA) -> String {
    let mut result = String::new();
    for info in nfa.state_list.iter() {
        let dist = info.backtrack_distance;
        match info.state {
            State::Leaf => { result.push_str(&format!("$ ({})", dist)); }
            State::Child => { result.push_str(&format!("> ({})", dist)); }
            State::Descendant => { result.push_str(&format!("_ ({})", dist)); }
            State::NextSibling => { result.push_str(&format!("+ ({})", dist)); }
            State::LaterSibling => { result.push_str(&format!("~ ({})", dist)); }
            _ => {}
        };
    }
    return result;
}

/*
fn build_transition_map(state_list: &Vec<State>)
                        -> HashMap<(usize, Symbol), usize> {

    let mut map = HashMap::new();

    let failed_idx = 1; // Index 1 is Failed

    for (state_idx, state) in state_list.iter().enumerate() {
        let next_state_idx = get_next_state_idx(state_idx, state_list);

        match state {
            &State::Leaf(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), next_state_idx);
                // If we do not match, we failed and can never match
                map.insert((state_idx, Symbol::NotMatched), failed_idx);
                // No epsilon transitions for leaf state
                // No end of stream for leaf state since we always at least
                // have a root node
            }
            &State::Child(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), next_state_idx);
                // If we do not match, we backtrack to a previous state
                // If we hit a sibling node, we skip it
                //map.insert((state_idx, Symbol::Epsilon),
                //           (!0, true));
                // If we reach the end of the parent nodes,
                // matching will never happen
                //map.insert((state_idx, Symbol::EndOfStream), failed_idx);
            }
            &State::Descendant(..) => {
                // If we match, we try the next state and retry with the
                // next node if the next state fails and backtracks
                map.insert((state_idx, Symbol::Matched), next_state_idx);
                // If we don't match, we skip the node
                //map.insert((state_idx, Symbol::NotMatched),
                //           (!0, true));
                // If we hit a sibling node, we skip it
                //map.insert((state_idx, Symbol::Epsilon),
                //           (!0, true));
                // If we reach the end of the parent nodes,
                // matching will never happen
                //map.insert((state_idx, Symbol::EndOfStream), failed_idx);
            }
            &State::NextSibling(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), next_state_idx);
                // If we do not match, we backtrack to a previous state
                // No epsilon transition for next sibling state
                // If we reach the end of the sibling nodes, we backtrack
            }
            &State::LaterSibling(..) => {
                // If we match, we try the next state and retry with the
                // next node if the next state fails and backtracks
                map.insert((state_idx, Symbol::Matched), next_state_idx);
                // If we don't match, we skip the node
                //map.insert((state_idx, Symbol::NotMatched),
                //           (!0, true));
                // No epsilon transition for later sibling state
                // If we reach the end of the sibling nodes, we backtrack
            }
            // These two states are our final accepting states
            &State::Matched => {}
            &State::Failed => {}
        }
    }

    //println!("DEBUG CSS RULE: [{}]", to_string(state_list));

    return map;
}
*/

pub fn build_nfa(selector: &CompoundSelector) -> SelectorNFA {

    let (state_list, selector_list) = get_states(selector);

    return SelectorNFA {
        state_list: state_list,
        selector_list: selector_list,
    };
}

fn is_rejected_by_bloom_filter(state_idx: usize, nfa: &SelectorNFA,
                               parent_bf: Option<&BloomFilter>,
                               hier_level: usize,
                               last_tested_hier_level: &mut usize)
                               -> bool {
    // The parent bloom filter holds whether or not some properties
    // might have been supported by the parent nodes.
    // Thus, if a particular descendant state matches with the bloom filter
    // at a particular node, all children nodes will also match but not
    // necessarily the parent nodes. But, if a particular descendant state
    // does NOT match with the bloom filter, no parent node can match since
    // they would remove information but children nodes could match.
    //
    // Since we iterate on nodes towards the parent, as soon as a descendant
    // state does not match, we can never match. Additionally, if our
    // descendant state matches, it will also match for all current siblings
    // since they share the same parent bloom filter. This means we only
    // need to test the bloom filter if the current state matches AND we
    // moved up in the hierarchy since the last test. Incidentally, if we
    // backtrack, we can cache the result since it will never change.

    let bf = match parent_bf {
        None => return false,
        Some(ref bf) => bf,
    };

    if hier_level <= *last_tested_hier_level {
        // We already tested this level. If we had been rejected we would have
        // terminated. We thus obviously still match.
        return false;
    }

    for next_state_idx in (state_idx + 1) .. nfa.state_list.len() {
        let ref info = nfa.state_list[next_state_idx];

        // TODO: See if we should test child states as well? Original impl
        // doesn't but is that correct?

        if info.state != State::Descendant { continue; }

        let start_idx = info.first_selector_idx;
        let end_idx = start_idx + info.num_selectors;

        for ss in &nfa.selector_list[start_idx .. end_idx] {
            match ss {
                &SimpleSelector::LocalName(LocalName { ref name, ref lower_name }) => {
                    if !bf.might_contain(name)
                    && !bf.might_contain(lower_name) {
                        return true;
                    }
                },
                &SimpleSelector::Namespace(ref namespace) => {
                    if !bf.might_contain(namespace) {
                        return true;
                    }
                },
                &SimpleSelector::ID(ref id) => {
                    if !bf.might_contain(id) {
                        return true;
                    }
                },
                &SimpleSelector::Class(ref class) => {
                    if !bf.might_contain(class) {
                        return true;
                    }
                },
                _ => {},
            };
        }
    }

    // Update our last tested level which also implies our last non-rejected
    // level
    *last_tested_hier_level = hier_level;

    return false;
}

#[inline(never)]
fn eval_selectors<E>(element: &E,
                     simple_selectors: &[SimpleSelector],
                     shareable: &mut bool, stats: &mut DebugStats)
                -> Symbol where E: Element {
    let all_matched = simple_selectors.iter().all(|sel| {
        matching::matches_simple_selector(sel, element, shareable, stats)
    });

    if !all_matched {
        return Symbol::NotMatched;
    }

    return Symbol::Matched;
}

#[inline]
fn get_symbol<E>(info: &StateInfo, nfa: &SelectorNFA, element: &E,
                 shareable: &mut bool, stats: &mut DebugStats)
                 -> Symbol where E: Element {

    let start_idx = info.first_selector_idx;
    let end_idx = start_idx + info.num_selectors;

    eval_selectors(element, &nfa.selector_list[start_idx .. end_idx],
                   shareable, stats)
}

#[inline]
fn get_matched_backtrack_distance(state_idx: usize) -> usize {
    // Matched is index 0
    return state_idx - 0;
}

#[inline]
fn get_not_matched_backtrack_distance(state_idx: usize) -> usize {
    // Failed is index 1
    return state_idx - 1;
}

fn eval_state<E>(state_idx: usize, nfa: &SelectorNFA,
                 mut hier_level: usize, last_tested_hier_level: &mut usize,
                 element: &E,
                 parent_bf: Option<&BloomFilter>,
                 shareable: &mut bool, stats: &mut DebugStats)
                 -> usize where E: Element {

    stats.num_fn_calls += 1;

    let ref info = nfa.state_list[state_idx];

    // Convert our input element into a symbol
    let symbol = get_symbol(&info, nfa, element, shareable, stats);

    let next_state_idx = match symbol {
        Symbol::Matched => {
            if is_rejected_by_bloom_filter(state_idx, nfa, parent_bf,
                                   hier_level, last_tested_hier_level) {
                // If the bloom filter rejects our descendant selectors,
                // we can never match
                return get_not_matched_backtrack_distance(state_idx);
            }
            if state_idx + 1 >= nfa.state_list.len() {
                // We fully matched
                return get_matched_backtrack_distance(state_idx);
            }
            state_idx + 1
        },
        // Back track
        Symbol::NotMatched => return info.backtrack_distance,
    };

    let ref next_info = nfa.state_list[next_state_idx];

    let mut next_element = match next_info.direction {
        Direction::Parent => {
            hier_level += 1;
            element.parent_element()
        },
        Direction::Sibling => element.prev_sibling_element(),
    };

    let end_of_stream_distance = match next_info.direction {
        Direction::Parent => get_not_matched_backtrack_distance(state_idx),
        Direction::Sibling => info.backtrack_distance,
    };

    loop {
        let element = match next_element {
            None => return end_of_stream_distance,
            Some(e) => e,
        };

        // Try our next state with the next element
        let distance = eval_state(next_state_idx, nfa,
                                  hier_level,
                                  last_tested_hier_level,
                                  &element, parent_bf,
                                  shareable, stats);

        if distance > 1 { return distance - 1; }

        next_element = match next_info.direction {
            Direction::Parent => {
                hier_level += 1;
                element.parent_element()
            },
            Direction::Sibling => element.prev_sibling_element(),
        };
    }
}

pub fn matches_nfa<E>(nfa: &SelectorNFA, element: &E,
                      parent_bf: Option<&BloomFilter>,
                      shareable: &mut bool,
                      stats: &mut DebugStats)
                      -> bool where E: Element {

    // TODO: Move the bloom filter test after our leaf test
    // If our leaf matches and we should test the bloom filter (add flag),
    // test it once. No point in testing it every time.
    // This means we need to move out the leaf test separaretly.

    let leaf_state_idx = 2;    // Index 2 is leaf

    // Start hierarchy level 1 above the last tested level to make
    // sure we test the first level
    let hier_level = 1;
    let mut last_tested_hier_level = 0;

    let distance = eval_state(leaf_state_idx, nfa, hier_level,
                              &mut last_tested_hier_level,
                              element, parent_bf, shareable, stats);

    // If we backtrack this far, it means we are backtracking towards one
    // of our 2 artificial states. Index 0 is Matched and Index 1 is Failed.
    // Thus if at the leaf our backtrack distance is 2, we are matched and
    // if it is 1, we failed. The distance cannot be any other value here.
    return distance == 2;
}

