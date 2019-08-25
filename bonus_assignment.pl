:- module(bonus_assignment, [canonical_covers/3]).
:- dynamic(leftred/1).  
:- dynamic(minimal/1).  

insAll(_, [], Zss, Zss).
insAll(X, [Ys|Yss], Zss, Xss) :-
  insAll(X, Yss, [[X|Ys]|Zss], Xss).

powerSet([], [[]]).
powerSet([X|Xs], PS) :-
  powerSet(Xs, P),
  insAll(X, P, P, PS), !.

subtract([], _, []) :- !.
subtract([E|T], D, R) :-
	memberchk(E, D), !,
	subtract(T, D, R).
subtract([H|T], D, [H|R]) :-
	subtract(T, D, R).
  
union([], L, L) :- !.
union([H|T], L, R) :-
	memberchk(H, L), !,
	union(T, L, R).
union([H|T], L, [H|R]) :-
	union(T, L, R).
  
union(Sets, USet) :-
  union2(Sets, [], USet).

union2([], USetAcc, USetAcc).
union2([H|T], USetAcc, USet) :-
  union(USetAcc, H, USetAcc0),
  union2(T, USetAcc0, USet).

subset([], _) :- !.
subset([H|T], Set) :-
	memberchk(H, Set),
	subset(T, Set).

foldl([X|Xs], Func, Y0, Y) :-
  call(Func, X, Y0, Y1), foldl(Xs, Func, Y1, Y).
foldl([], _, Y, Y).

foldr([X|Xs], Func, Y0, Y) :-
  foldr(Xs, Func, Y0, Y1), call(Func, X, Y1, Y).
foldr([], _, Y, Y).

% mapping function
map([X|Xs], Func, [Y|Ys]) :-
  call(Func, X, Y), map(Xs, Func, Ys).
map([], _, []).

% convert chars to list 
% cover <---> [c, o, v, e, r]
chars_to_list(A, L) :- 
  ( atom(L) -> A = L
  ; atom_chars(A, L)
  ).

list_of_chars_to_list([], []) :- !.
list_of_chars_to_list([A|As], [L|Ls]) :-
  chars_to_list(A, L),
  list_of_chars_to_list(As, Ls).

% from list to string in FD
% EXAMPLE: merge_chars([[a,b]->c],X). RESULT: X = [(ab->c)].
merge_chars(FC, FP) :-
  map(FC, bonus_assignment:merge_chars_helper, FP).
  
merge_chars_helper(XL->YL, XA->YA) :-
  chars_to_list(XA, XL),
  chars_to_list(YA, YL).
  
% from string to list in FD
% EXAMPLE: split_chars([(ab->c)],X). RESULT: X = [([a, b]->[c])].
split_chars(FC, FP) :-
  map(FC, bonus_assignment:split_chars_helper, FP).

split_chars_helper(C, P) :-
  merge_chars_helper(P, C).


% alpha_plus EXAMPLE: alpha_plus([a],[[a]->[b],[a]->[c]],X). RESULT: X = [a, [c], [b]].
alpha_plus(X, F, APlus) :-
  ( X = [] -> APlus = []
  ; foldr(F, bonus_assignment:expand_attributes, X, X0),
    ( X = X0 -> APlus = X0
    ; alpha_plus(X0, F, APlus)
    )
  ).

% expanded set of attributes  EXAMPLE: expand_attributes([a]->[b,c],[a],X). RESULT: X = [a, [b, c]].
expand_attributes(Y->Z, X, X0) :-
  ( subset(Y, X) -> union(X, [Z], X0) % Y is a subset of X
  ; X0 = X % cannot expand
  ).


% returns non reducible on left side
% EXAMPLE: non_reducible([a,b]->c,[[a]->c],X). RESULT: X = [a] ;
non_reducible(X->A, F, Y) :-
  left_redundant(X, X->A, F, Y).
  
left_redundant([H|T], X->A, F, Y) :-
  subtract(X, [H], X0),
  alpha_plus(X0, F, X0C),
  ( memberchk(A, X0C), Y = X0
  ; left_redundant(T, X->A, F, Y)
  ). 


% 1st step of minimalizing
% confirm single attribute on right side
% EXAMPLE: split_right([a->[b,c]],X). RESULT: X = [(a->b),  (a->c)].
split_right(F, F1) :-
  foldl(F, bonus_assignment:split_right_helper, [], F0),
  lists:reverse(F0, F1).

split_right_helper(X->Y, F, F1) :-
  ( Y = [H|T] -> split_right_helper(X->T, [X->H|F], F1)
  ; F1 = F
  ).

% 2nd step of minimalizing
% remove reducible attributes from the left side 
% EXAMPLE: minimalizeLeft([[a,b]->c,[a]->c,[b]->c], X). RESULT: X = [([a]->c),  ([b]->c)] ;
minimalizeLeft(F, LeftRedundant) :-
  retractall(leftred(_)),
  minimalizeLeft(F, F, LeftRedundant, false).

minimalizeLeft([], LeftRedundant, LeftRedundant, false) :- \+ leftred(LeftRedundant), assert(leftred(LeftRedundant)).
minimalizeLeft([X->A|T], F, LeftRedundant, Flag) :-
  ( non_reducible(X->A, F, _),
    subtract(F, [X->A], F0),
    union(F0, [_->A], F1),
    ( minimalizeLeft(F1, LeftRedundant)
    ; minimalizeLeft(T, F, LeftRedundant, true)
    )
  ; \+ non_reducible(X->A, F, _), minimalizeLeft(T, F, LeftRedundant, Flag)
  ).

% 3rd step of minimalizing
% skip deducible attributes
% EXAMPLE: skip_redundant([[a]->a], FMin). RESULT: FMin = [] ; from reflexivity
% EXAMPLE: skip_redundant([[a,b]->a], FMin). RESULT: FMin = [] ;
skip_redundant(F, FMin) :-
  skip_redundant(F, F, FMin, false).
  
% we may skip X->A if A is in (APlus)+(H), where H is F \ {X->A}
skip_redundant([], FReduced, FReduced, false).
skip_redundant([X->A|T], F, FReduced, Flag) :-
  subtract(F, [X->A], G),                   
  alpha_plus(X, G, APlus),                     
  ( memberchk(A, APlus) ->                 
    ( skip_redundant(G, FReduced)
    ; skip_redundant(T, F, FReduced, true)
    )
  ; skip_redundant(T, F, FReduced, Flag)
  ). 

canonical_cover(F, FMin) :-
  retractall(minimal(_)),
  split_right(F, F1),
  minimalizeLeft(F1, F2),
  skip_redundant(F2, F3),
  sort(F3, FMin),
  \+ minimal(FMin), assert(minimal(FMin)).

without_trivial([], _, []).
without_trivial([H|T], F, FPlus) :-
  without_trivial(T, F, Tail),
  alpha_plus(H, F, Head),
  subtract(Head, H, NonTrivialHead),
  ( NonTrivialHead = [] -> FPlus = Tail
  ; FPlus = [H->NonTrivialHead|Tail]
  ).

create_closure(R, F, FPlus) :-
  powerSet(R, RP),
  without_trivial(RP, F, FPlus0),
  split_right(FPlus0, FPlus).


% calculate the closure of a set 
closure(R, F, FPlus) :-
  chars_to_list(R, R0),
  split_chars(F, F0),
  split_right(F0, F1),
  create_closure(R0, F1, FPlus0),
  merge_chars(FPlus0, FPlus). 


% ========= find canonical covers ==========
canonical_covers(Chars , F, Fmin) :-
  closure(Chars, F , F0) , 
  split_chars(F0, F1), 
  canonical_cover(F1, F2),
  merge_chars(F2, Fmin).
