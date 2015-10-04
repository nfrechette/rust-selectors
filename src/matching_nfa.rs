/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

extern crate time as stdtime;

use parser::{CompoundSelector, Combinator, SimpleSelector};
use matching::{self, DebugStats};
use tree::Element;
use std::collections::HashMap;

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

#[derive(PartialEq, Clone, Debug)]
pub struct SelectorNFA {
    pub state_list: Vec<State>,
    pub transition_map: HashMap<(u32, Symbol), Vec<u32>>,
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

fn get_next_state_idx(idx: usize, state_list: &Vec<State>) -> u32 {
    if idx + 1 >= state_list.len() {
        return 0;  // Index 0 is Matched
    }
    else {
        return idx as u32 + 1;
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
                        -> HashMap<(u32, Symbol), Vec<u32>> {

    let mut map = HashMap::new();

    let failed_idx: u32 = 1; // Index 1 is Failed

    for (state_idx, state) in state_list.iter().enumerate() {
        let next_state_idx = get_next_state_idx(state_idx, state_list);
        let state_idx = state_idx as u32;

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

pub fn build_nfa(selector: &CompoundSelector) -> SelectorNFA {

    let state_list = get_states(selector);

    let map = build_transition_map(&state_list);

    return SelectorNFA {
        state_list: state_list,
        transition_map: map,
    };
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum InputValue {
    Parent,
    Sibling,
    Leaf,
}

fn eval_selectors<E>(simple_selectors: &[SimpleSelector],
                     element: &E, shareable: &mut bool,
                     stats: &mut DebugStats)
                     -> Symbol where E: Element {
    let all_matched = simple_selectors.iter().all(|sel| {
        matching::matches_simple_selector(sel, element, shareable, stats)
    });

    if all_matched {
        return Symbol::Matched;
    }
    else {
        return Symbol::NotMatched;
    }
}

fn eval_leaf<E>(simple_selectors: &[SimpleSelector],
                input_value: InputValue, element: Option<&E>,
                shareable: &mut bool, stats: &mut DebugStats)
                 -> Symbol where E: Element {
    let element = match element {
        None => panic!(),
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => panic!(),
        InputValue::Sibling => panic!(),
        InputValue::Leaf => eval_selectors(simple_selectors, element,
                                           shareable, stats),
    }
}

fn eval_descendant<E>(simple_selectors: &[SimpleSelector],
                      input_value: InputValue, element: Option<&E>,
                      shareable: &mut bool, stats: &mut DebugStats)
                      -> Symbol where E: Element {
    let element = match element {
        None => return Symbol::EndOfStream,
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => eval_selectors(simple_selectors, element,
                                             shareable, stats),
        InputValue::Sibling => Symbol::Epsilon,
        InputValue::Leaf => panic!(),
    }
}

fn eval_sibling<E>(simple_selectors: &[SimpleSelector],
                   input_value: InputValue, element: Option<&E>,
                   shareable: &mut bool, stats: &mut DebugStats)
                   -> Symbol where E: Element {
    let element = match element {
        None => return Symbol::EndOfStream,
        Some(e) => e,
    };
    match input_value {
        InputValue::Parent => Symbol::EndOfStream,
        InputValue::Sibling => eval_selectors(simple_selectors, element,
                                              shareable, stats),
        InputValue::Leaf => panic!(),
    }
}

fn get_symbol<E>(state: &State, input_value: InputValue,
                 element: Option<&E>,
                 shareable: &mut bool, stats: &mut DebugStats)
                 -> Symbol where E: Element {
    match state {
        &State::Leaf(ref simple_selectors) =>
            eval_leaf(simple_selectors, input_value, element,
                      shareable, stats),
        &State::Child(ref simple_selectors) |
        &State::Descendant(ref simple_selectors) =>
            eval_descendant(simple_selectors, input_value, element,
                            shareable, stats),
        &State::NextSibling(ref simple_selectors) |
        &State::LaterSibling(ref simple_selectors) =>
            eval_sibling(simple_selectors, input_value, element,
                         shareable, stats),
        _ => panic!(),
    }
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum EvaluationResult {
    Matched,
    NotMatched,
    Backtrack,
}

fn accepts_ref<E>(state_idx: u32, nfa: &SelectorNFA,
                  input_value: InputValue, element: Option<&E>,
                  shareable: &mut bool, stats: &mut DebugStats)
                  -> EvaluationResult where E: Element {
    let ref state = nfa.state_list[state_idx as usize];

    // Check if we are a final accepting state
    match state {
        &State::Matched => return EvaluationResult::Matched,
        &State::Failed => return EvaluationResult::NotMatched,
        _ => {}
    };

    // Convert our input element into a symbol
    let symbol = get_symbol(state, input_value, element,
                            shareable, stats);

    // Look up our possible transitions and try them
    let transitions = nfa.transition_map.get(&(state_idx, symbol));

    match transitions {
        None => {},
        Some(transitions) => {
            let mut next_element = element.map_or(None, |e| e.prev_sibling_element());
            let mut next_value = InputValue::Sibling;
            if next_element.is_none() {
                next_element = element.map_or(None, |e| e.parent_element());
                next_value = InputValue::Parent;
            }

            for next_state in transitions.iter() {
                let result = accepts_ref(*next_state, nfa, next_value,
                                         next_element.as_ref(),
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

fn needs_parent(state_idx: u32, nfa: &SelectorNFA) -> bool {
    let ref state = nfa.state_list[state_idx as usize];
    match state {
        &State::Child(..) |
        &State::Descendant(..) => true,
        _ => false,
    }
}

fn accepts<E>(state_idx: u32, nfa: &SelectorNFA,
              input_value: InputValue, element: Option<&E>,
              shareable: &mut bool, stats: &mut DebugStats)
              -> EvaluationResult where E: Element {
    let ref state = nfa.state_list[state_idx as usize];

    // Check if we are a final accepting state
    match state {
        &State::Matched => return EvaluationResult::Matched,
        &State::Failed => return EvaluationResult::NotMatched,
        _ => {}
    };

    // Convert our input element into a symbol
    let symbol = get_symbol(state, input_value, element,
                            shareable, stats);

    // Look up our possible transitions and try them
    let transitions = nfa.transition_map.get(&(state_idx, symbol));

    match transitions {
        None => {},
        Some(transitions) => {
            for next_state in transitions.iter() {
                let needs_parent = needs_parent(*next_state, nfa);
                let (next_element, next_value) = if needs_parent {
                    (element.map_or(None, |e| e.parent_element()),
                     InputValue::Parent)
                } else {
                    (element.map_or(None, |e| e.prev_sibling_element()),
                     InputValue::Sibling)
                };

                let result = accepts_ref(*next_state, nfa, next_value,
                                         next_element.as_ref(),
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

pub fn matches_nfa_ref<E>(nfa: &SelectorNFA, element: &E,
                          shareable: &mut bool,
                          stats: &mut DebugStats)
                          -> bool where E: Element {
    let leaf_state_idx = 2;    // Index 2 is leaf
    let result = accepts_ref(leaf_state_idx, nfa, InputValue::Leaf,
                             Some(element), shareable, stats);
    return result == EvaluationResult::Matched;
}

pub fn matches_nfa_opt<E>(nfa: &SelectorNFA, element: &E,
                          shareable: &mut bool,
                          stats: &mut DebugStats)
                          -> bool where E: Element {
    let leaf_state_idx = 2;    // Index 2 is leaf
    let result = accepts(leaf_state_idx, nfa, InputValue::Leaf,
                         Some(element), shareable, stats);
    return result == EvaluationResult::Matched;
}

pub fn matches_nfa<E>(nfa: &SelectorNFA, element: &E,
                      shareable: &mut bool,
                      stats: &mut DebugStats)
                      -> bool where E: Element {
    //return matches_nfa_ref(nfa, element, shareable, stats);
    return matches_nfa_opt(nfa, element, shareable, stats);
}

