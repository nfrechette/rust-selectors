/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

extern crate time as stdtime;

use parser::{CompoundSelector, Combinator, SimpleSelector};
use matching::{self, DebugInfo};
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
enum State<'a> {
    Leaf(&'a Vec<SimpleSelector>),
    Child(&'a Vec<SimpleSelector>),
    Descendant(&'a Vec<SimpleSelector>),
    NextSibling(&'a Vec<SimpleSelector>),
    LaterSibling(&'a Vec<SimpleSelector>),
    Matched,
    Failed,
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum Symbol {
    Matched,
    NotMatched,
    Epsilon,
    EndOfStream,
}

struct SelectorNFA<'a> {
    transition_map: HashMap<(&'a State<'a>, Symbol), Vec<&'a State<'a>>>,
}

fn get_states_internal<'a, 'b>(selector: &'a CompoundSelector,
                       state_list: &'b mut Vec<State<'a>>) {

    let state = match selector.next {
        None => return,
        Some((ref next_selector, Combinator::Child))
            => State::Child(&next_selector.simple_selectors),
        Some((ref next_selector, Combinator::Descendant))
            => State::Descendant(&next_selector.simple_selectors),
        Some((ref next_selector, Combinator::NextSibling))
            => State::NextSibling(&next_selector.simple_selectors),
        Some((ref next_selector, Combinator::LaterSibling))
            => State::LaterSibling(&next_selector.simple_selectors),
    };

    state_list.push(state);

    match selector.next {
        None => return,
        Some((ref next, _)) => get_states_internal(&**next, state_list),
    };
}

fn get_states<'a>(selector: &'a CompoundSelector) -> Vec<State<'a>> {
    let mut state_list = vec!();

    state_list.push(State::Matched);
    state_list.push(State::Failed);
    state_list.push(State::Leaf(&selector.simple_selectors));

    get_states_internal(selector, &mut state_list);

    return state_list;
}

fn get_next_state<'a>(idx: usize, state_list: &'a Vec<State>) -> &'a State<'a> {
    if idx + 1 >= state_list.len() {
        return &state_list[0];  // Index 0 is Matched
    }
    else {
        return &state_list[idx + 1];
    }
}

fn build_transition_map<'a, 'b>(state_list: &'a Vec<State<'a>>,
                        map: &'b mut HashMap<(&'a State<'a>, Symbol), Vec<&'a State<'a>>>) {

    let ref failed = state_list[1]; // Index 1 is Failed

    for idx in 0 .. state_list.len() {
        let ref state = state_list[idx];
        let next_state = get_next_state(idx, state_list);

        match state {
            &State::Leaf(..) => {
                map.insert((state, Symbol::Matched), vec![next_state]);
                map.insert((state, Symbol::NotMatched), vec![failed]);
            }
            &State::Child(..) => {
                map.insert((state, Symbol::Matched), vec![next_state]);
                map.insert((state, Symbol::Epsilon), vec![state]);
                map.insert((state, Symbol::EndOfStream), vec![failed]);
            }
            &State::Descendant(..) => {
                map.insert((state, Symbol::Matched), vec![next_state, state]);
                map.insert((state, Symbol::NotMatched), vec![state]);
                map.insert((state, Symbol::Epsilon), vec![state]);
                map.insert((state, Symbol::EndOfStream), vec![failed]);
            }
            &State::NextSibling(..) => {
                map.insert((state, Symbol::Matched), vec![next_state]);
            }
            &State::LaterSibling(..) => {
                map.insert((state, Symbol::Matched), vec![next_state, state]);
                map.insert((state, Symbol::NotMatched), vec![state]);
                // TODO: Prune matched epsilon transition in special cases
            }
            &State::Matched => {}
            &State::Failed => {}
        }
    }
}

fn build_nfa<'a>(state_list: &'a Vec<State<'a>>) -> SelectorNFA {
    let mut nfa = SelectorNFA {
        transition_map: HashMap::new(),
    };

    build_transition_map(state_list, &mut nfa.transition_map);

    return nfa;
}

#[derive(Eq, PartialEq, Clone, Hash, Copy, Debug)]
enum InputValue {
    Parent,
    Sibling,
    Leaf,
    EndOfStream,
}

fn eval_selectors<E>(simple_selectors: &[SimpleSelector],
                     element: &E, shareable: &mut bool,
                     debug_info: &mut DebugInfo)
                     -> Symbol where E: Element {
    let all_matched = simple_selectors.iter().all(|sel| {
        matching::matches_simple_selector(sel, element, shareable, debug_info)
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
                shareable: &mut bool, debug_info: &mut DebugInfo)
                 -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => panic!(),
        InputValue::Sibling => panic!(),
        InputValue::Leaf => eval_selectors(simple_selectors, element,
                                           shareable, debug_info),
        InputValue::EndOfStream => panic!(),
    }
}

fn eval_descendant<E>(simple_selectors: &[SimpleSelector],
                      input_value: InputValue, element: &E,
                      shareable: &mut bool, debug_info: &mut DebugInfo)
                      -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => eval_selectors(simple_selectors, element,
                                             shareable, debug_info),
        InputValue::Sibling => Symbol::Epsilon,
        InputValue::Leaf => panic!(),
        InputValue::EndOfStream => Symbol::EndOfStream,
    }
}

fn eval_sibling<E>(simple_selectors: &[SimpleSelector],
                   input_value: InputValue, element: &E,
                   shareable: &mut bool, debug_info: &mut DebugInfo)
                   -> Symbol where E: Element {
    match input_value {
        InputValue::Parent => Symbol::EndOfStream,
        InputValue::Sibling => eval_selectors(simple_selectors, element,
                                              shareable, debug_info),
        InputValue::Leaf => panic!(),
        InputValue::EndOfStream => Symbol::EndOfStream,
    }
}

fn get_symbol<'a, E>(state: &'a State, input_value: InputValue,
                     element: &'a E,
                     shareable: &mut bool, debug_info: &mut DebugInfo)
                     -> Symbol where E: Element {
    match state {
        &State::Leaf(ref simple_selectors) =>
            eval_leaf(simple_selectors, input_value, element,
                      shareable, debug_info),
        &State::Child(ref simple_selectors) |
        &State::Descendant(ref simple_selectors) =>
            eval_descendant(simple_selectors, input_value, element,
                            shareable, debug_info),
        &State::NextSibling(ref simple_selectors) |
        &State::LaterSibling(ref simple_selectors) =>
            eval_sibling(simple_selectors, input_value, element,
                         shareable, debug_info),
        _ => panic!(),
    }
}

fn accepts<'a, E>(state: &'a State, nfa: &'a SelectorNFA,
                  input_value: InputValue, element: &'a E,
                  shareable: &mut bool, debug_info: &mut DebugInfo)
                  -> bool where E: Element {
    match state {
        &State::Matched => return true,
        &State::Failed => return false,
        _ => {}
    };

    let symbol = get_symbol(state, input_value, element,
                            shareable, debug_info);

    if symbol == Symbol::EndOfStream {
        return false;
    }

    let transitions = nfa.transition_map.get(&(state, symbol));

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
                        // Re-use the same element since we have
                        // a valid reference to it, it won't get used
                        accepts(*next_state, nfa,
                                InputValue::EndOfStream, element,
                                shareable, debug_info),
                    Some(ref next_element) =>
                        accepts(*next_state, nfa,
                                next_value, next_element,
                                shareable, debug_info),
                };

                if result {
                    return true;
                }
            }
        }
    };

    return false;

}

pub fn matches_nfa<E>(selector: &CompoundSelector,
                      element: &E,
                      shareable: &mut bool,
                      debug_info: &mut DebugInfo)
                      -> bool
                      where E: Element {

    let state_list = get_states(selector);

    let nfa = build_nfa(&state_list);

    *shareable = false;

    let initial_state = State::Leaf(&selector.simple_selectors);
    return accepts(&initial_state, &nfa, InputValue::Leaf, element,
                   shareable, debug_info);
}

