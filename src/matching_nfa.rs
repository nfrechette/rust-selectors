/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

extern crate time as stdtime;

use parser::{CompoundSelector, Combinator, SimpleSelector, LocalName};
use matching::{self, DebugStats};
use tree::Element;
use std::collections::HashMap;
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

#[derive(Eq, PartialEq, Clone, Hash, Debug)]
pub enum State {
    Leaf(Vec<SimpleSelector>),
    Child(Vec<SimpleSelector>),
    Descendant(Vec<SimpleSelector>),
    NextSibling(Vec<SimpleSelector>),
    LaterSibling(Vec<SimpleSelector>),
    Matched,
    Failed,
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
pub enum Symbol {
    Matched,
    NotMatched,
    Epsilon,
    EndOfStream,
}

fn get_symbol_index(symbol: Symbol) -> usize {
    match symbol {
        Symbol::Matched =>      0,
        Symbol::NotMatched =>   1,
        Symbol::Epsilon =>      2,
        Symbol::EndOfStream =>  3,
    }
}

static NUM_SYMBOLS: usize = 4;

#[derive(PartialEq, Clone, Debug)]
pub struct SelectorNFA {
    // Store the list of NFA states including the simple selectors (copied)
    pub state_list: Vec<State>,

    // Simple transition map: (current state idx, symbol) -> next state idx list
    pub transition_map: HashMap<(usize, Symbol), Vec<usize>>,

    // Compact transition map:
    // Each transition leads to at most 2 states, a new state and the current
    // state (epsilon transition). We use a u8 to store this. If the MSB is
    // set, we have an epsilon transition otherwise we do not. The rest of
    // the bits store the next state index. 7 bits allow for 128 states.
    // The size of the array is Num States * Num Symbols
    pub compact_transition_map: Vec<u8>,
}

fn get_states_internal(selector: &CompoundSelector,
                       state_list: &mut Vec<State>) {

    let state = match selector.next {
        None => return,
        Some((ref next_selector, Combinator::Child))
            => State::Child(next_selector.simple_selectors.to_vec()),
        Some((ref next_selector, Combinator::Descendant))
            => State::Descendant(next_selector.simple_selectors.to_vec()),
        Some((ref next_selector, Combinator::NextSibling))
            => State::NextSibling(next_selector.simple_selectors.to_vec()),
        Some((ref next_selector, Combinator::LaterSibling))
            => State::LaterSibling(next_selector.simple_selectors.to_vec()),
    };

    state_list.push(state);

    match selector.next {
        None => return,
        Some((ref next, _)) => get_states_internal(&**next, state_list),
    };
}

fn get_states(selector: &CompoundSelector) -> Vec<State> {
    let mut state_list = vec!();

    state_list.push(State::Matched);
    state_list.push(State::Failed);
    state_list.push(State::Leaf(selector.simple_selectors.to_vec()));

    get_states_internal(selector, &mut state_list);

    return state_list;
}

fn get_next_state_idx(idx: usize, state_list: &Vec<State>) -> usize {
    if idx + 1 >= state_list.len() {
        return 0;  // Index 0 is Matched
    }
    else {
        return idx + 1;
    }
}

pub fn to_string(state_list: &Vec<State>) -> String {
    let mut result = String::new();
    for state in state_list.iter() {
        match state {
            &State::Leaf(..) => { result.push_str("$"); }
            &State::Child(..) => { result.push_str(">"); }
            &State::Descendant(..) => { result.push_str(" "); }
            &State::NextSibling(..) => { result.push_str("+"); }
            &State::LaterSibling(..) => { result.push_str("~"); }
            _ => {}
        };
    }
    return result;
}

fn build_transition_map(state_list: &Vec<State>)
                        -> HashMap<(usize, Symbol), Vec<usize>> {

    let mut map = HashMap::new();

    let failed_idx = 1; // Index 1 is Failed

    for (state_idx, state) in state_list.iter().enumerate() {
        let next_state_idx = get_next_state_idx(state_idx, state_list);

        match state {
            &State::Leaf(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
                // If we do not match, we failed and can never match
                map.insert((state_idx, Symbol::NotMatched), vec![failed_idx]);
                // No epsilon transitions for leaf state
                // No end of stream for leaf state since we always at least
                // have a root node
            }
            &State::Child(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
                // If we do not match, we backtrack to a previous state
                // If we hit a sibling node, we skip it
                map.insert((state_idx, Symbol::Epsilon), vec![state_idx]);
                // If we reach the end of the parent nodes,
                // matching will never happen
                map.insert((state_idx, Symbol::EndOfStream), vec![failed_idx]);
            }
            &State::Descendant(..) => {
                // If we match, we try the next state and retry with the
                // next node if the next state fails and backtracks
                map.insert((state_idx, Symbol::Matched),
                           vec![next_state_idx, state_idx]);
                // If we don't match, we skip the node
                map.insert((state_idx, Symbol::NotMatched), vec![state_idx]);
                // If we hit a sibling node, we skip it
                map.insert((state_idx, Symbol::Epsilon), vec![state_idx]);
                // If we reach the end of the parent nodes,
                // matching will never happen
                map.insert((state_idx, Symbol::EndOfStream), vec![failed_idx]);
            }
            &State::NextSibling(..) => {
                // If we match, move on to the next state
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
                // If we do not match, we backtrack to a previous state
                // No epsilon transition for next sibling state
                // If we reach the end of the sibling nodes, we backtrack
            }
            &State::LaterSibling(..) => {
                // If we match, we try the next state and retry with the
                // next node if the next state fails and backtracks
                map.insert((state_idx, Symbol::Matched),
                           vec![next_state_idx, state_idx]);
                // If we don't match, we skip the node
                map.insert((state_idx, Symbol::NotMatched), vec![state_idx]);
                // No epsilon transition for later sibling state
                // If we reach the end of the sibling nodes, we backtrack
            }
            // These two states are our final accepting states
            &State::Matched => {}
            &State::Failed => {}
        }
    }

    //println!("DEBUG CSS RULE: [{}]", to_string(state_list));
/*
    // Prune epsilon transitions for early-out conditions
    for (state_idx, state) in state_list.iter().enumerate() {
        match state {
            &State::LaterSibling(..) => {
                let mut cursor_idx = state_idx + 1;
                while cursor_idx < state_list.len() {
                    match &state_list[cursor_idx] {
                        &State::NextSibling(..) => { cursor_idx += 1; }
                        _ => { break; }
                    };
                }

                if cursor_idx < state_list.len() {
                    match &state_list[cursor_idx] {
                        &State::Child(..) => {
                            println!("Early out from child at {}. [{}]", cursor_idx, to_string(state_list));
                            let cursor_idx = cursor_idx as u32;
                            let ls = map.get_mut(&(cursor_idx, Symbol::Matched));
                            ls.unwrap().pop();
                        }
                        _ => {}
                    };
                }
            }
            _ => {}
        };
    }
*/

    return map;
}

fn build_compact_transition_map(state_list: &Vec<State>,
                        transition_map: &HashMap<(usize, Symbol), Vec<usize>>)
                        -> Vec<u8> {
    // TODO: Right now we panic if we have too many states, in practice
    // we would want to detect this and fallback to the reference impl.
    if state_list.len() > 128 { panic!(); }

    let compact_map_size = state_list.len() * NUM_SYMBOLS;
    let mut compact_map = vec![!0u8; compact_map_size];

    let symbols = [Symbol::Matched, Symbol::NotMatched,
                   Symbol::Epsilon, Symbol::EndOfStream];

    for (state_idx, _) in state_list.iter().enumerate() {
        for symbol in symbols.iter() {
            let symbol_idx = get_symbol_index(*symbol);
            let map_idx = (state_idx * NUM_SYMBOLS) + symbol_idx;
            let key = (state_idx, *symbol);

            let transitions = transition_map.get(&key);
            let transition = match transitions {
                None => !0u8,
                Some(transitions) => {
                    let mut transition = transitions[0] as u8;
                    if transitions.len() > 1 {
                        // TODO: Convert to asserts?
                        if transitions.len() > 2 { panic!(); }
                        if transitions[1] != state_idx { panic!(); }

                        // Epsilon transition
                        transition |= 1 << 7;
                    }
                    transition
                },
            };

            compact_map[map_idx] = transition;
        }
    }

    return compact_map;
}

pub fn build_nfa(selector: &CompoundSelector) -> SelectorNFA {

    let state_list = get_states(selector);

    let map = build_transition_map(&state_list);
    let compact_map = build_compact_transition_map(&state_list, &map);

    return SelectorNFA {
        state_list: state_list,
        transition_map: map,
        compact_transition_map: compact_map,
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

    for next_state_idx in state_idx + 1 .. nfa.state_list.len() {
        let ref state = nfa.state_list[next_state_idx];

        // TODO: See if we should test child states as well? Original impl
        // doesn't but is that correct?

        let ref simple_selectors = match state {
            &State::Descendant(ref simple_selectors) => simple_selectors,
            _ => continue,
        };

        for ss in simple_selectors.iter() {
            match *ss {
                SimpleSelector::LocalName(LocalName { ref name, ref lower_name }) => {
                    if !bf.might_contain(name)
                    && !bf.might_contain(lower_name) {
                        return true;
                    }
                },
                SimpleSelector::Namespace(ref namespace) => {
                    if !bf.might_contain(namespace) {
                        return true;
                    }
                },
                SimpleSelector::ID(ref id) => {
                    if !bf.might_contain(id) {
                        return true;
                    }
                },
                SimpleSelector::Class(ref class) => {
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

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum InputValue {
    Parent,
    Sibling,
    Leaf,
}

fn eval_selectors<E>(state_idx: usize, nfa: &SelectorNFA,
                     hier_level: usize,
                     last_tested_hier_level: &mut usize,
                     element: &E, parent_bf: Option<&BloomFilter>,
                     simple_selectors: &[SimpleSelector],
                     shareable: &mut bool, stats: &mut DebugStats)
                -> Symbol where E: Element {
    let all_matched = simple_selectors.iter().all(|sel| {
        matching::matches_simple_selector(sel, element, shareable, stats)
    });

    if !all_matched {
        return Symbol::NotMatched;
    }

    if is_rejected_by_bloom_filter(state_idx, nfa, parent_bf,
                                   hier_level, last_tested_hier_level) {
        // If the bloom filter rejects our descendant selectors, simulate
        // the end of the stream since we can never match
        return Symbol::EndOfStream;
    }

    return Symbol::Matched;
}

fn eval_leaf<E>(state_idx: usize, nfa: &SelectorNFA,
                hier_level: usize,
                last_tested_hier_level: &mut usize,
                input_value: InputValue, element: Option<&E>,
                parent_bf: Option<&BloomFilter>,
                simple_selectors: &[SimpleSelector],
                shareable: &mut bool, stats: &mut DebugStats)
            -> Symbol where E: Element {
    let element = match element {
        None => panic!(),
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => panic!(),
        InputValue::Sibling => panic!(),
        InputValue::Leaf => eval_selectors(state_idx, nfa, hier_level,
                                           last_tested_hier_level,
                                           element, parent_bf,
                                           simple_selectors,
                                           shareable, stats),
    }
}

fn eval_descendant<E>(state_idx: usize, nfa: &SelectorNFA,
                      hier_level: usize,
                      last_tested_hier_level: &mut usize,
                      input_value: InputValue, element: Option<&E>,
                      parent_bf: Option<&BloomFilter>,
                      simple_selectors: &[SimpleSelector],
                      shareable: &mut bool, stats: &mut DebugStats)
                   -> Symbol where E: Element {
    let element = match element {
        None => return Symbol::EndOfStream,
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => eval_selectors(state_idx, nfa, hier_level,
                                             last_tested_hier_level,
                                             element, parent_bf,
                                             simple_selectors,
                                             shareable, stats),
        InputValue::Sibling => Symbol::Epsilon,
        InputValue::Leaf => panic!(),
    }
}

fn eval_sibling<E>(state_idx: usize, nfa: &SelectorNFA,
                   hier_level: usize,
                   last_tested_hier_level: &mut usize,
                   input_value: InputValue, element: Option<&E>,
                   parent_bf: Option<&BloomFilter>,
                   simple_selectors: &[SimpleSelector],
                   shareable: &mut bool, stats: &mut DebugStats)
                -> Symbol where E: Element {
    let element = match element {
        None => return Symbol::EndOfStream,
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => Symbol::EndOfStream,
        InputValue::Sibling => eval_selectors(state_idx, nfa, hier_level,
                                              last_tested_hier_level,
                                              element, parent_bf,
                                              simple_selectors,
                                              shareable, stats),
        InputValue::Leaf => panic!(),
    }
}

fn get_symbol<E>(state_idx: usize, nfa: &SelectorNFA,
                 hier_level: usize,
                 last_tested_hier_level: &mut usize,
                 input_value: InputValue, element: Option<&E>,
                 parent_bf: Option<&BloomFilter>,
                 shareable: &mut bool, stats: &mut DebugStats)
                 -> Symbol where E: Element {
    let ref state = nfa.state_list[state_idx];

    match state {
        &State::Leaf(ref simple_selectors) =>
            eval_leaf(state_idx, nfa, hier_level,
                      last_tested_hier_level, input_value, element,
                      parent_bf, simple_selectors, shareable, stats),
        &State::Child(ref simple_selectors) |
        &State::Descendant(ref simple_selectors) =>
            eval_descendant(state_idx, nfa, hier_level,
                            last_tested_hier_level, input_value, element,
                            parent_bf, simple_selectors, shareable, stats),
        &State::NextSibling(ref simple_selectors) |
        &State::LaterSibling(ref simple_selectors) =>
            eval_sibling(state_idx, nfa, hier_level,
                         last_tested_hier_level, input_value, element,
                         parent_bf, simple_selectors, shareable, stats),
        _ => panic!(),
    }
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum EvaluationResult {
    Matched,
    NotMatched,
    Backtrack,
}

fn accepts_ref<E>(state_idx: usize, nfa: &SelectorNFA,
                  hier_level: usize, last_tested_hier_level: &mut usize,
                  input_value: InputValue, element: Option<&E>,
                  parent_bf: Option<&BloomFilter>,
                  shareable: &mut bool, stats: &mut DebugStats)
                  -> EvaluationResult where E: Element {
    let ref state = nfa.state_list[state_idx];

    // Check if we are a final accepting state
    match state {
        &State::Matched => return EvaluationResult::Matched,
        &State::Failed => return EvaluationResult::NotMatched,
        _ => {}
    };

    // Convert our input element into a symbol
    let symbol = get_symbol(state_idx, nfa,
                            hier_level, last_tested_hier_level,
                            input_value, element, parent_bf,
                            shareable, stats);

    // Look up our possible transitions and try them
    let transitions = nfa.transition_map.get(&(state_idx, symbol));

    match transitions {
        None => {},
        Some(transitions) => {
            let mut next_element = element.map_or(None, |e| e.prev_sibling_element());
            let mut next_value = InputValue::Sibling;
            let mut next_hier_level = hier_level;
            if next_element.is_none() {
                next_element = element.map_or(None, |e| e.parent_element());
                next_value = InputValue::Parent;
                next_hier_level += 1;
            }

            for next_state in transitions.iter() {
                let result = accepts_ref(*next_state, nfa, next_hier_level,
                                         last_tested_hier_level,
                                         next_value,
                                         next_element.as_ref(), parent_bf,
                                         shareable, stats);

                if result != EvaluationResult::Backtrack {
                    // If we aren't backtracking, return
                    return result;
                }
            }
        }
    };

    // If we didn't find a transition or if they all asked to backtrack,
    // we backtrack
    return EvaluationResult::Backtrack;
}

fn needs_parent(state_idx: usize, nfa: &SelectorNFA) -> bool {
    let ref state = nfa.state_list[state_idx];
    match state {
        &State::Child(..) |
        &State::Descendant(..) => true,
        _ => false,
    }
}

fn accepts_opt<E>(state_idx: usize, nfa: &SelectorNFA,
                  hier_level: usize, last_tested_hier_level: &mut usize,
                  input_value: InputValue, element: Option<&E>,
                  parent_bf: Option<&BloomFilter>,
                  shareable: &mut bool, stats: &mut DebugStats)
              -> EvaluationResult where E: Element {
    let ref state = nfa.state_list[state_idx];

    // Check if we are a final accepting state
    match state {
        &State::Matched => return EvaluationResult::Matched,
        &State::Failed => return EvaluationResult::NotMatched,
        _ => {}
    };

    // Convert our input element into a symbol
    let symbol = get_symbol(state_idx, nfa,
                            hier_level, last_tested_hier_level,
                            input_value, element, parent_bf,
                            shareable, stats);

    // Look up our possible transitions and try them
    let symbol_idx = get_symbol_index(symbol);
    let transition_idx = (state_idx * NUM_SYMBOLS) + symbol_idx;
    let transitions = nfa.compact_transition_map[transition_idx];

    if transitions == !0 {
        // No transitions, backtrack!
        return EvaluationResult::Backtrack;
    }

    // Try our next state first
    {
        let next_state_idx = (transitions & !(1 << 7)) as usize;
        let needs_parent = needs_parent(next_state_idx, nfa);
        let (next_element, next_value, next_hier_level) = if needs_parent {
            (element.map_or(None, |e| e.parent_element()),
             InputValue::Parent, hier_level + 1)
        } else {
            (element.map_or(None, |e| e.prev_sibling_element()),
             InputValue::Sibling, hier_level)
        };

        let result = accepts_opt(next_state_idx, nfa, next_hier_level,
                                 last_tested_hier_level, next_value,
                                 next_element.as_ref(), parent_bf,
                                 shareable, stats);

        if result != EvaluationResult::Backtrack {
            // If we aren't backtracking, return
            return result;
        }
    }

    if (transitions & (1 << 7)) == 0 {
        // No epsilon transition and our next state transition backtracked
        return EvaluationResult::Backtrack;
    }

    // Now try the epsilon transition to our current state
    {
        let next_state_idx = state_idx;
        let needs_parent = needs_parent(next_state_idx, nfa);
        let (next_element, next_value, next_hier_level) = if needs_parent {
            (element.map_or(None, |e| e.parent_element()),
             InputValue::Parent, hier_level + 1)
        } else {
            (element.map_or(None, |e| e.prev_sibling_element()),
             InputValue::Sibling, hier_level)
        };

        let result = accepts_opt(next_state_idx, nfa, next_hier_level,
                                 last_tested_hier_level, next_value,
                                 next_element.as_ref(), parent_bf,
                                 shareable, stats);

        if result != EvaluationResult::Backtrack {
            // If we aren't backtracking, return
            return result;
        }
    }

    // Everything backtracked, we backtrack
    return EvaluationResult::Backtrack;
}

pub fn matches_nfa_ref<E>(nfa: &SelectorNFA, element: &E,
                          parent_bf: Option<&BloomFilter>,
                          shareable: &mut bool,
                          stats: &mut DebugStats)
                          -> bool where E: Element {
    let leaf_state_idx = 2;    // Index 2 is leaf

    // Start hierarchy level 1 above the last tested level to make
    // sure we test the first level
    let hier_level = 1;
    let mut last_tested_hier_level = 0;

    let result = accepts_ref(leaf_state_idx, nfa, hier_level,
                             &mut last_tested_hier_level, InputValue::Leaf,
                             Some(element), parent_bf, shareable, stats);

    return result == EvaluationResult::Matched;
}

pub fn matches_nfa_opt<E>(nfa: &SelectorNFA, element: &E,
                          parent_bf: Option<&BloomFilter>,
                          shareable: &mut bool,
                          stats: &mut DebugStats)
                          -> bool where E: Element {
    let leaf_state_idx = 2;    // Index 2 is leaf

    // Start hierarchy level 1 above the last tested level to make
    // sure we test the first level
    let hier_level = 1;
    let mut last_tested_hier_level = 0;

    let result = accepts_opt(leaf_state_idx, nfa, hier_level,
                             &mut last_tested_hier_level, InputValue::Leaf,
                             Some(element), parent_bf, shareable, stats);

    return result == EvaluationResult::Matched;
}

pub fn matches_nfa<E>(nfa: &SelectorNFA, element: &E,
                      parent_bf: Option<&BloomFilter>,
                      shareable: &mut bool,
                      stats: &mut DebugStats)
                      -> bool where E: Element {
    //return matches_nfa_ref(nfa, element, parent_bf, shareable, stats);
    return matches_nfa_opt(nfa, element, parent_bf, shareable, stats);
}

