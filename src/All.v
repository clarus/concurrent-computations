(** Experiments for the "composable monads" project. *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.String.

Import ListNotations.
Local Open Scope string_scope.

Set Implicit Arguments.

Module Monad.
  Record t := New {
    S : Type;
    E : Type }.
End Monad.

Module Result.
  Inductive t (A B C : Type) : Type :=
  | Val : A -> t A B C
  | Err : B -> t A B C
  | Mon : C -> t A B C.

  Arguments Val {A B C} _.
  Arguments Err {A B C} _.
  Arguments Mon {A B C} _.
End Result.

Module M.
  Inductive t (m : Monad.t) (A : Type) : Type :=
  | New : (Monad.S m -> Result.t A (Monad.E m) (t m A) * Monad.S m) -> t m A.

  Definition open (m : Monad.t) A (x : t m A)
    : Monad.S m -> Result.t A (Monad.E m) (t m A) * Monad.S m :=
    match x with
    | New x' => x'
    end.
End M.

Module Id.
  Definition m : Monad.t :=
    Monad.New unit Empty_set.
End Id.

Definition ret {m : Monad.t} A (x : A) : M.t m A :=
  M.New (fun s => (Result.Val x, s)).

Fixpoint bind {m : Monad.t} A B (x : M.t m A) (f : A -> M.t m B) : M.t m B :=
  M.New (fun s =>
    match M.open x s with
    | (Result.Val x, s) => (Result.Mon (f x), s)
    | (Result.Err e, s) => (Result.Err e, s)
    | (Result.Mon x, s) => (Result.Mon (bind x f), s)
    end).

Definition seq {m : Monad.t} A B (x : M.t m A) (f : M.t m B) : M.t m B :=
  bind x (fun _ => f).

Fixpoint run {m : Monad.t} A (x : M.t m A) (s : Monad.S m)
  : (A + Monad.E m) * Monad.S m :=
  match M.open x s with
  | (Result.Val x, s) => (inl x, s)
  | (Result.Err e, s) => (inr e, s)
  | (Result.Mon x, s) => run x s
  end.

Definition combine (m1 m2 : Monad.t) : Monad.t :=
  Monad.New (Monad.S m1 * Monad.S m2) (Monad.E m1 + Monad.E m2).

Infix "++" := combine.

Fixpoint combine_id (m : Monad.t) A (x : M.t (Id.m ++ m) A) : M.t m A :=
  M.New (fun s =>
    match M.open x (tt, s) with
    | (Result.Val x, (_, s)) => (Result.Val x, s)
    | (Result.Err (inr e), (_, s)) => (Result.Err e, s)
    | (Result.Err (inl e), _) => match e with end
    | (Result.Mon x, (_, s)) => (Result.Mon (combine_id x), s)
    end).

Fixpoint combine_commut (m1 m2 : Monad.t) A (x : M.t (m1 ++ m2) A)
  : M.t (m2 ++ m1) A :=
  M.New (m := m2 ++ m1) (fun s =>
    let (s2, s1) := s in
    match M.open x (s1, s2) with
    | (Result.Val x, (s1, s2)) => (Result.Val x, (s2, s1))
    | (Result.Err e, (s1, s2)) =>
      (Result.Err (match e with
      | inl e1 => inr e1
      | inr e2 => inl e2
      end), (s2, s1))
    | (Result.Mon x', (s1, s2)) => (Result.Mon (combine_commut x'), (s2, s1))
    end).

Fixpoint combine_assoc_left (m1 m2 m3 : Monad.t) A (x : M.t ((m1 ++ m2) ++ m3) A)
  : M.t (m1 ++ (m2 ++ m3)) A :=
  M.New (m := m1 ++ (m2 ++ m3)) (fun s =>
    match s with
    | (s1, (s2, s3)) =>
      match M.open x ((s1, s2), s3) with
      | (Result.Val x, ((s1, s2), s3)) => (Result.Val x, (s1, (s2, s3)))
      | (Result.Err e, ((s1, s2), s3)) =>
        let e := match e with
          | inl (inl e1) => inl e1
          | inl (inr e2) => inr (inl e2)
          | inr e3 => inr (inr e3)
          end in
        (Result.Err e, (s1, (s2, s3)))
      | (Result.Mon x, ((s1, s2), s3)) => (Result.Mon (combine_assoc_left x), (s1, (s2, s3)))
      end
    end).

Fixpoint combine_assoc_right (m1 m2 m3 : Monad.t) A (x : M.t (m1 ++ (m2 ++ m3)) A)
  : M.t ((m1 ++ m2) ++ m3) A :=
  M.New (m := (m1 ++ m2) ++ m3) (fun s =>
    match s with
    | ((s1, s2), s3) =>
      match M.open x (s1, (s2, s3)) with
      | (Result.Val x, (s1, (s2, s3))) => (Result.Val x, ((s1, s2), s3))
      | (Result.Err e, (s1, (s2, s3))) =>
        let e := match e with
          | inl e1 => inl (inl e1)
          | inr (inl e2) => inl (inr e2)
          | inr (inr e3) => inr e3
          end in
        (Result.Err e, ((s1, s2), s3))
      | (Result.Mon x, (s1, (s2, s3))) => (Result.Mon (combine_assoc_right x), ((s1, s2), s3))
      end
    end).

Fixpoint lift {m m' : Monad.t} A (x : M.t m' A) : M.t (m ++ m') A :=
  M.New (m := m ++ m') (fun s =>
    let (s1, s2) := s in
    match M.open x s2 with
    | (Result.Val x, s2) => (Result.Val x, (s1, s2))
    | (Result.Err e, s2) => (Result.Err (inr e), (s1, s2))
    | (Result.Mon x, s2) => (Result.Mon (lift x), (s1, s2))
    end).

Module Option.
  Definition m : Monad.t :=
    Monad.New unit unit.

  Definition none {A} : M.t m A :=
    M.New (m := m) (fun _ => (Result.Err tt, tt)).

  Definition run {A} (x : M.t m A) : option A :=
    match run x tt with
    | (inl x, _) => Some x
    | _ => None
    end.
End Option.

Module Error.
  Definition m (E : Type) : Monad.t :=
    Monad.New unit E.

  Definition raise {E A} (e : E) : M.t (m E) A :=
    M.New (m := m E) (fun _ => (Result.Err e, tt)).
End Error.

Module Print.
  Definition m (A : Type) : Monad.t :=
    Monad.New (list A) Empty_set.

  Definition print {A} (x : A) : M.t (m A) unit :=
    M.New (m := m A) (fun s =>
      (Result.Val tt, x :: s)).
End Print.

Module State.
  Definition m (S : Type) : Monad.t :=
    Monad.New S Empty_set.

  Definition read {S : Type} : M.t (m S) S :=
    M.New (m := m S) (fun s => (Result.Val s, s)).

  Definition write {S : Type} (x : S) : M.t (m S) unit :=
    M.New (m := m S) (fun _ => (Result.Val tt, x)).
End State.

Module Loop.
  Definition m : Monad.t :=
    Monad.New nat unit.
End Loop.

Fixpoint local_run {m m' : Monad.t} A (x : M.t (m ++ m') A) (s_m : Monad.S m)
  : M.t (Error.m (Monad.E m) ++ m') A :=
  M.New (m := Error.m (Monad.E m) ++ m') (fun s =>
    let (_, s_m') := s in
    match M.open x (s_m, s_m') with
    | (r, (s_m, s_m')) =>
      let r := match r with
        | Result.Val x => Result.Val x
        | Result.Err e => Result.Err e
        | Result.Mon x => Result.Mon (local_run x s_m)
        end in
      (r, (tt, s_m'))
    end).

(** Breaks *)
Module Breaker.
  Definition m : Monad.t :=
    Monad.New bool Empty_set.

  Definition break : M.t m unit :=
    M.New (m := m) (fun _ => (Result.Val tt, true)).

  Fixpoint local_run {m' : Monad.t} {A} (x : M.t (m ++ m') A)
    : M.t m' (A + M.t (m ++ m') A) :=
    M.New (m := m') (fun i =>
      match M.open x (false, i) with
      | (r, (true, o)) =>
        (Result.Val (inr (M.New (m := m ++ m') (fun i =>
          (r, (false, snd i))))), o)
      | (Result.Val x, (false, o)) => (Result.Val (inl x), o)
      | (Result.Err e, (false, o)) =>
        match e with
        | inl e_break => match e_break with end
        | inr e_m => (Result.Err e_m, o)
        end
      | (Result.Mon x, (false, o)) => (Result.Mon (local_run x), o)
      end).

  Fixpoint local_run_n {m' : Monad.t} {A} (x : M.t (m ++ m') A)
    (a : M.t m' unit) (n : nat) : M.t m' (A + M.t (m ++ m') A) :=
    match n with
    | 0 => ret (inr x)
    | Datatypes.S n' => bind (local_run x) (fun x =>
      match x with
      | inl x => ret (inl x)
      | inr x => seq a (local_run_n x a n')
      end)
    end.

  Fixpoint local_run_terminate {m' : Monad.t} {A}
    (x : M.t (m ++ m') A) (a : M.t m' unit) : M.t m' A :=
    M.New (m := m') (fun i =>
      match M.open x (false, i) with
      | (Result.Val x, (_, o)) => (Result.Val x, o)
      | (Result.Err e, (_, o)) =>
        match e with
        | inl e_break => match e_break with end
        | inr e_m => (Result.Err e_m, o)
        end
      | (Result.Mon x, (_, o)) => (Result.Mon (seq a (local_run_terminate x a)), o)
      end).
End Breaker.

(** Coroutines *)
Definition Waiter (m : Monad.t) (A B : Type) : Monad.t :=
  Breaker ++ State ((A -> M.t m B) * bool).

Module Coroutine.
  Definition t {m : Monad.t} (A B T : Type) := M.t (Waiter m A B ++ m) T.

  Definition break_if_not_fresh {m : Monad.t} A B : t A B unit :=
    combine_commut (gret (
      bind (m := Waiter m A B) (gret (read _)) (fun f_fresh =>
        let (_, fresh) := f_fresh in
        if fresh then
          ret tt
        else
          combine_commut (gret break)))).

  Definition use_and_consume {m : Monad.t} A B (a : A) : t A B B :=
    combine_assoc_right (gret (combine_commut (
      bind (m := m ++ State _) (gret (read _)) (fun f_fresh : _ * _ =>
        let (f, _) := f_fresh in
        seq (gret (write (f, false)))
          (combine_commut (gret (f a))))))).

  Definition yield {m : Monad.t} A B (a : A) : t A B B :=
    seq (break_if_not_fresh _ _) (use_and_consume _ a).

  (*Definition I_of_O {m : Monad.t} A B (o : @O (Waiter m A B)) : option (@I (Waiter m A B)) :=
    match o with
    | ((f, fresh), break) =>
      if break then
        None
      else
        Some (f, fresh)
    end.*)

  (*Definition inject_new_f {m : Monad.t} A B (f : A -> M.t m B) : M.t (State ((A -> M.t m B) * bool)) unit :=
    write (f, true).*)

  (*Definition force {m : Monad.t} A B T (x : t A B T) (f : A -> M.t m B) : M.t (T + t A B T) :=
    local_run (m' := m) (local_run_with_break x) (fun o => o) (f, true).

  Definition force {m : Monad.t} A B T (x : t A B T) (f : A -> M.t m B) : M.t (T + t A B T) :=
    sum_id (local_run_with_break x (I_of_O (B := _)) (f, true)).

  Definition force_n {m : Monad.t} A B T (x : t A B T) (n : nat) (f : A -> M.t m B) : M.t (T + t A B T) :=
    sum_id (local_run_with_break_n x (I_of_O (B := _)) (f, true) n).

  Definition terminate {m : Monad.t} A B T (x : t A B T) (f : A -> M.t m B) : M.t T :=
    sum_id (local_run_with_break_terminate x (I_of_O (B := _)) (f, true)).
End Coroutine.

Fixpoint iter_list {m : Monad.t} A (l : list A) : Coroutine.t A unit unit :=
  match l with
  | nil => ret tt
  | x :: l' => seq (Coroutine.yield _ x) (iter_list l')
  end.

Definition test_it {m : Monad.t} := iter_list [1; 5; 7; 2].

Definition test1 := Coroutine.terminate test_it (fun x => print x).
Compute run test1 (fun o => o) nil.

Definition test2 n := seq
  (Coroutine.force_n test_it n (fun x => print x))
  (ret tt).
Definition test2_run n := run (test2 n) (fun o => o) nil.
Compute test2_run 0.
Compute test2_run 1.
Compute test2_run 2.
Compute test2_run 3.
Compute test2_run 4.
Compute test2_run 5.

Definition test3 := Coroutine.terminate test_it (fun x =>
  if eq_nat_dec x 7 then
    gret (m := Print nat) (raise _ "x is equal to 7")
  else
    combine_commut (gret (m := Error.m string) (print x))).

Compute run test3 (fun o => o) (nil, tt).

(** Cooperative threads *)
Definition Breaker : Monad.t := {
  I := Stream bool;
  E := Empty_set;
  O := Stream bool * bool; (* if we did a break *)
  O_of_I := fun s => (s, false)}.

Definition break : M.t Breaker unit :=
  M.New (fun s =>
    (inl (inl tt), (Streams.tl s, Streams.hd s))).

Fixpoint join_aux {m : Monad.t} A B (x : M.t (Breaker ++ m) A) :=
  fix aux (y : M.t (Breaker ++ m) B) (left_first : bool) : M.t (Breaker ++ m) (A * B):=
    if left_first then
      M.New (fun i =>
        match (M.open x) i with
        | (inl xe, o) =>
          match xe with
          | inl x => (inr (bind y (fun y => ret (x, y))), o)
          | inr e => (inl (inr e), o)
          end
        | (inr x, ((s, breaking), o)) =>
          if breaking then
            (inr (join_aux _ x y false), ((s, false), o))
          else
            (inr (join_aux _ x y true), ((s, false), o))
        end)
    else
      M.New (fun i =>
        match (M.open y) i with
        | (inl ye, o) =>
          match ye with
          | inl y => (inr (bind x (fun x => ret (x, y))), o)
          | inr e => (inl (inr e), o)
          end
        | (inr y, ((s, breaking), o)) =>
          if breaking then
            (inr (aux y true), ((s, false), o))
          else
            (inr (aux y false), ((s, false), o))
        end).

Definition join {m : Monad.t} A B (x : M.t (Breaker ++ m) A) (y : M.t (Breaker ++ m) B)
  : M.t (Breaker ++ m) (A * B) :=
  join_aux x y true.

(* join (print 12; break; print 13) (print 23; break; print 0) *)
Definition test4 := join
  (seq (gret (print 12)) (seq (combine_commut (gret break)) (gret (print 13))))
  (seq (gret (print 23)) (seq (combine_commut (gret break)) (gret (print 0)))).

Definition test4_run s :=
  run test4 (fun o => let (sb, o) := o in (fst sb, o)) (s, nil).

Compute test4_run (Streams.const false).
Compute test4_run (Streams.const true).*)

(*Fixpoint local_run_with_break {m m' : Monad.t} A
  (x : M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m)
  : M.t (Error.m (Monad.E m) ++ m') (A + M.t (m ++ m') A) :=
  M.New (m := Error.m (Monad.E m) ++ m') (fun i =>
    let (_, i_m') := i in
    match M.open x (i_m, i_m') with
    | (inl xe, (o_m, o_m')) =>
      let o := (tt, o_m') in
      match xe with
      | inl x => (inl (inl (inl x)), o)
      | inr (inl e_m) => (inl (inr (inl e_m)), o)
      | inr (inr e_m') => (inl (inr (inr e_m')), o)
      end
    | (inr x, (o_m, o_m')) =>
      let o := (tt, o_m') in
      match I_of_O o_m with
      | Some i'_m => (inr (local_run_with_break x I_of_O i'_m), o)
      | None => (inl (inl (inr x)), o)
      end
    end).

Fixpoint local_run_with_break_n {m m' : Monad.t} A
  (x : M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m) (n : nat)
  : M.t (Error.m (Monad.E m) ++ m') (A + M.t (m ++ m') A) :=
  match n with
  | 0 => ret (inr x)
  | S n' => bind (local_run_with_break x I_of_O i_m) (fun x =>
    match x with
    | inl r => ret (inl r)
    | inr x => local_run_with_break_n x I_of_O i_m n'
    end)
  end.

Definition local_run_with_break_terminate {m m' : Monad.t} A
  (x : M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m)
  : M.t (Error.m (Monad.E m) ++ m') A :=
  let fix aux (x : M.t (m ++ m') A) (i'_m : @I m) : M.t (Error.m (Monad.E m) ++ m') A :=
    M.New (m := Error.m (Monad.E m) ++ m') (fun i =>
      let (_, i_m') := i in
      match (M.open x) (i'_m, i_m') with
      | (inl xe, (o_m, o_m')) =>
        let o := (tt, o_m') in
        match xe with
        | inl x => (inl (inl x), o)
        | inr (inl e_m) => (inl (inr (inl e_m)), o)
        | inr (inr e_m') => (inl (inr (inr e_m')), o)
        end
      | (inr x, (o_m, o_m')) =>
        let o := (tt, o_m') in
        match I_of_O o_m with
        | Some i'_m => (inr (aux x i'_m), o)
        | None => (inr (aux x i_m), o)
        end
      end) in
  aux x i_m.*)
