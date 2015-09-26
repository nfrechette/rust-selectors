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

fn build_transition_map(state_list: &Vec<State>)
                        -> HashMap<(u32, Symbol), Vec<u32>> {

    let mut map = HashMap::new();

    let failed_idx: u32 = 1; // Index 1 is Failed

    for state_idx in 0 .. state_list.len() {
        let ref state = state_list[state_idx];
        let next_state_idx = get_next_state_idx(state_idx, state_list);
        let state_idx: u32 = state_idx as u32;

        match state {
            &State::Leaf(..) => {
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
                map.insert((state_idx, Symbol::NotMatched), vec![failed_idx]);
            }
            &State::Child(..) => {
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
                map.insert((state_idx, Symbol::Epsilon), vec![state_idx]);
                map.insert((state_idx, Symbol::EndOfStream), vec![failed_idx]);
            }
            &State::Descendant(..) => {
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx, state_idx]);
                map.insert((state_idx, Symbol::NotMatched), vec![state_idx]);
                map.insert((state_idx, Symbol::Epsilon), vec![state_idx]);
                map.insert((state_idx, Symbol::EndOfStream), vec![failed_idx]);
            }
            &State::NextSibling(..) => {
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx]);
            }
            &State::LaterSibling(..) => {
                map.insert((state_idx, Symbol::Matched), vec![next_state_idx, state_idx]);
                map.insert((state_idx, Symbol::NotMatched), vec![state_idx]);
                // TODO: Prune matched epsilon transition in special cases
            }
            &State::Matched => {}
            &State::Failed => {}
        }
    }

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
                input_value: InputValue, element: &E,
                shareable: &mut bool, stats: &mut DebugStats)
                 -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => panic!(),
        InputValue::Sibling => panic!(),
        InputValue::Leaf => eval_selectors(simple_selectors, element,
                                           shareable, stats),
    }
}

fn eval_descendant<E>(simple_selectors: &[SimpleSelector],
                      input_value: InputValue, element: &E,
                      shareable: &mut bool, stats: &mut DebugStats)
                      -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => eval_selectors(simple_selectors, element,
                                             shareable, stats),
        InputValue::Sibling => Symbol::Epsilon,
        InputValue::Leaf => panic!(),
    }
}

fn eval_sibling<E>(simple_selectors: &[SimpleSelector],
                   input_value: InputValue, element: &E,
                   shareable: &mut bool, stats: &mut DebugStats)
                   -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => Symbol::EndOfStream,
        InputValue::Sibling => eval_selectors(simple_selectors, element,
                                              shareable, stats),
        InputValue::Leaf => panic!(),
    }
}

fn get_symbol<E>(state: &State, input_value: InputValue,
                 element: &E,
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

fn accepts<E>(state_idx: u32, nfa: &SelectorNFA,
              input_value: InputValue, element: &E,
              shareable: &mut bool, stats: &mut DebugStats)
              -> bool where E: Element {
    let ref state = nfa.state_list[state_idx as usize];

    match state {
        &State::Matched => return true,
        &State::Failed => return false,
        _ => {}
    };

    let symbol = get_symbol(state, input_value, element,
                            shareable, stats);

    if symbol == Symbol::EndOfStream {
        return false;
    }

    let transitions = nfa.transition_map.get(&(state_idx, symbol));

    match transitions {
        None => {},
        Some(transitions) => {
            let mut next_element = element.prev_sibling_element();
            let mut next_value = InputValue::Sibling;
            if next_element.is_none() {
                next_element = element.parent_element();
                next_value = InputValue::Parent;
            }

            for next_state in transitions.iter() {
                let result = match next_element {
                    None =>
                        nfa.state_list[*next_state as usize] == State::Matched,
                    Some(ref next_element) =>
                        accepts(*next_state, nfa,
                                next_value, next_element,
                                shareable, stats),
                };

                if result {
                    return true;
                }
            }
        }
    };

    return false;

}

pub fn matches_nfa<E>(nfa: &SelectorNFA, element: &E,
                      shareable: &mut bool,
                      stats: &mut DebugStats)
                      -> bool
                      where E: Element {
    *shareable = false;

    let leaf_state_idx: u32 = 2;    // Index 2 is leaf
    return accepts(leaf_state_idx, nfa, InputValue::Leaf, element,
                   shareable, stats);
}

