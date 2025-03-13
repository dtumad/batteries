/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Batteries.Control.Lawful.MonadLift
import Batteries.Control.AlternativeMonad


/-!
# Laws for Monadic Operations on Lists

This file contains lemmas about monadic operations on lists like the monadic mapping `List.mapM`
and monadic folds `List.foldlM` / `List.foldrM`

## Tags

monad, list
-/

namespace List

section MonadLift

theorem monadLift_mapM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : α → m β) (xs : List α) :
    monadLift (xs.mapM f) = xs.mapM (monadLift ∘ f : α → n β) := by
  induction xs with | nil => simp only [mapM_nil, liftM_pure] | cons _ _ h => simp [h]

@[simp] theorem liftM_mapM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : α → m β) (xs : List α) :
    liftM (xs.mapM f) = xs.mapM (liftM ∘ f : α → n β) := monadLift_mapM f xs

theorem monadLift_foldlM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : s → α → m s) (init : s) (xs : List α) :
    monadLift (xs.foldlM f init) = (xs.foldlM (fun x s => monadLift (f x s)) init : n s) := by
  revert init
  induction xs with | nil => simp | cons _ _ h => simp [h]

@[simp] theorem liftM_foldlM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : s → α → m s) (init : s) (xs : List α) :
    liftM (xs.foldlM f init) = (xs.foldlM (fun x s => liftM (f x s)) init : n s) :=
  monadLift_foldlM f init xs

theorem monadLift_foldrM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : α → s → m s) (init : s) (xs : List α) :
    monadLift (xs.foldrM f init) = (xs.foldrM (fun s x => monadLift (f s x)) init : n s) := by
  revert init
  induction xs with | nil => simp | cons _ _ h => simp [h]

@[simp] theorem liftM_foldrM [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] (f : α → s → m s) (init : s) (xs : List α) :
    liftM (xs.foldrM f init) = (xs.foldrM (fun s x => liftM (f s x)) init : n s) :=
  monadLift_foldrM f init xs

theorem monadLift_firstM [Alternative m] [Alternative n]
    [MonadLift m n] [LawfulAlternativeLift m n] (f : α → m β) (xs : List α) :
    monadLift (xs.firstM f) = xs.firstM (monadLift ∘ f : α → n β) := by
  induction xs with | nil => simp | cons x xs h => simp [h]

@[simp] theorem liftM_firstM [Alternative m] [Alternative n]
    [MonadLift m n] [LawfulAlternativeLift m n] (f : α → m β) (xs : List α) :
    liftM (xs.firstM f) = xs.firstM (liftM ∘ f : α → n β) := monadLift_firstM f xs

theorem monadLift_anyM [Monad m] [Monad n] [MonadLift m n] [LawfulMonadLift m n]
    (f : α → m Bool) (xs : List α) : monadLift (xs.anyM f) = xs.anyM (monadLift ∘ f : α → n Bool) := by
  induction xs with | nil => simp | cons _ _ h => ?_
  simp only [anyM, liftM_bind, Function.comp_apply]
  exact bind_congr fun | true => by simp | false => by simp [h]

@[simp] theorem liftM_anyM [Monad m] [Monad n] [MonadLift m n] [LawfulMonadLift m n]
    (f : α → m Bool) (xs : List α) : liftM (xs.anyM f) = xs.anyM (liftM ∘ f : α → n Bool) :=
  monadLift_anyM f xs

theorem monadLift_allM [Monad m] [Monad n] [MonadLift m n] [LawfulMonadLift m n]
    (f : α → m Bool) (xs : List α) : monadLift (xs.allM f) = xs.allM (monadLift ∘ f : α → n Bool) := by
  induction xs with | nil => simp | cons _ _ h => ?_
  simp only [allM, liftM_bind, Function.comp_apply]
  exact bind_congr fun | true => by simp [h] | false => by simp

@[simp] theorem liftM_allM [Monad m] [Monad n] [MonadLift m n] [LawfulMonadLift m n]
    (f : α → m Bool) (xs : List α) : liftM (xs.allM f) = xs.allM (liftM ∘ f : α → n Bool) :=
  monadLift_allM f xs

end MonadLift

end List
