-- File corrispondente alle sezioni 6.1 e 6.2


-- 6.1 — Il linguaggio IMP in Lean 4
-- ===========================================================
-- Sintassi astratta: Aexp, Bexp e Com come tipi induttivi.


-- Nomi delle variabili del linguaggio
abbrev Vname := String


-- Numeri naturali
abbrev Val := Nat


-- Stato del programma
abbrev State := Vname → Val


-- Espressioni aritmetiche
inductive Aexp where
  | N : Val → Aexp
  | V : Vname → Aexp
  | Plus : Aexp → Aexp → Aexp
deriving Repr


-- Espressioni booleane
inductive Bexp where
  | Bc : Bool → Bexp
  | Not : Bexp → Bexp
  | And : Bexp → Bexp → Bexp
  | Less : Aexp → Aexp → Bexp
deriving Repr


-- Comandi del linguaggio IMP
inductive Com where
  | Skip   : Com
  | Assign : Vname → Aexp → Com
  | Seq    : Com → Com → Com
  | If     : Bexp → Com → Com → Com
  | While  : Bexp → Com → Com
deriving Repr


-- Notazione più agevole per assegnamento e sequenza
notation:60 v " ::= " a => Com.Assign v a
notation:50 c1 " ;; " c2 => Com.Seq c1 c2


-- Valutazione di un'espressione aritmetica
-- rispetto a uno stato del programma.
def aval : Aexp → State → Val
  | Aexp.N n,        _ => n
  | Aexp.V x,        s => s x
  | Aexp.Plus a1 a2, s =>
      aval a1 s + aval a2 s


-- Valutazione di un'espressione booleana
-- rispetto a uno stato del programma.
def bval : Bexp → State → Bool
  | Bexp.Bc v,       _ => v
  | Bexp.Not b,      s =>
      !(bval b s)
  | Bexp.And b1 b2,  s =>
      bval b1 s && bval b2 s
  | Bexp.Less a1 a2, s =>
      aval a1 s < aval a2 s


-- Aggiornamento funzionale dello stato:
-- nello stato risultante x vale v; le altre variabili non cambiano.
def upd (s : State) (x : Vname) (v : Val) : State :=
  fun y => if y = x then v else s y


-- Notazione per lo stato aggiornato
notation:65 s "[" x " ↦ " v "]" => upd s x v


-- 6.2 — La semantica operazionale come relazione induttiva


-- c / s ==> s2 significa:
-- il comando c, eseguito nello stato s, termina nello stato s2.
-- La relazione descrive la semantica big-step del linguaggio IMP.
inductive BigStep : Com → State → State → Prop where

  -- Skip non modifica lo stato
  | Skip {s : State} :
      BigStep Com.Skip s s

  -- L'assegnamento aggiorna x con il valore dell'espressione a
  | Assign {x : Vname} {a : Aexp} {s : State} :
      BigStep (Com.Assign x a) s (s[x ↦ aval a s])

  -- Per una sequenza: si esegue c1 e poi c2 nello stato prodotto da c1.
  | Seq {c1 c2 : Com} {s1 s2 s3 : State} :
      BigStep c1 s1 s2 → BigStep c2 s2 s3 →
      BigStep (Com.Seq c1 c2) s1 s3

  -- Se la guardia è vera, viene eseguito il primo ramo.
  | IfTrue {b : Bexp} {c1 c2 : Com} {s s' : State} :
      bval b s = true → BigStep c1 s s' →
      BigStep (Com.If b c1 c2) s s'

  -- Se la guardia è falsa, viene eseguito il secondo ramo.
  | IfFalse {b : Bexp} {c1 c2 : Com} {s s' : State} :
      bval b s = false → BigStep c2 s s' →
      BigStep (Com.If b c1 c2) s s'

  -- Un ciclo termina subito se la guardia è falsa.
  | WhileFalse {b : Bexp} {c : Com} {s : State} :
      bval b s = false →
      BigStep (Com.While b c) s s

  -- Se la guardia è vera, si esegue il corpo e si prosegue con il ciclo dallo stato ottenuto.
  | WhileTrue {b : Bexp} {c : Com} {s1 s2 s3 : State} :
      bval b s1 = true →
      BigStep c s1 s2 →
      BigStep (Com.While b c) s2 s3 →
      BigStep (Com.While b c) s1 s3


-- Notazione per una derivazione big-step
notation:55 c " / " s " ==> " s2 => BigStep c s s2


-- Determinismo della semantica big-step:
-- a parità di comando e stato iniziale, il risultato finale è unico
-- Induzione sulla prima derivazione h₁
-- In ogni caso si analizza la seconda derivazione h₂
theorem bigstep_deterministic {c : Com} {s s₁ s₂ : State}
    (h₁ : c / s ==> s₁) (h₂ : c / s ==> s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with

  -- Skip può terminare soltanto lasciando invariato lo stato
  | Skip =>
      cases h₂ with
      | Skip =>
          rfl

  -- Anche un assegnamento ha un unico stato risultante
  | Assign =>
      cases h₂ with
      | Assign =>
          rfl

  -- Nella sequenza, si dimostra prima l'uguaglianza
  -- degli stati intermedi e poi quella degli stati finali
  | Seq h₁₁ h₁₂ ih₁ ih₂ =>
      cases h₂ with
      | Seq h₂₁ h₂₂ =>
          have hs := ih₁ h₂₁
          subst hs
          exact ih₂ h₂₂

  -- Una stessa guardia non può essere insieme vera e falsa
  -- Se è vera, entrambe le derivazioni eseguono il primo ramo
  | IfTrue ht h₁ ih =>
      cases h₂ with
      | IfTrue _ h₂ =>
          exact ih h₂
      | IfFalse hf _ =>
          rw [ht] at hf
          exact absurd hf (by decide)

  -- Caso simmetrico: se la guardia è falsa,
  -- entrambe le derivazioni eseguono il secondo ramo
  | IfFalse hf h₁ ih =>
      cases h₂ with
      | IfTrue ht _ =>
          rw [hf] at ht
          exact absurd ht (by decide)
      | IfFalse _ h₂ =>
          exact ih h₂

  -- Se la guardia del ciclo è falsa, il ciclo lascia lo stato invariato
  -- L'alternativa WhileTrue porterebbe a una contraddizione
  | WhileFalse hf =>
      cases h₂ with
      | WhileFalse _ =>
          rfl
      | WhileTrue ht _ _ =>
          rw [hf] at ht
          exact absurd ht (by decide)

  -- Se la guardia è vera, le due esecuzioni del corpo
  -- raggiungono lo stesso stato intermedio per ipotesi induttiva
  -- L'ipotesi induttiva sul ciclo conclude poi sugli stati finali
  | WhileTrue ht h₁₁ h₁₂ ih₁ ih₂ =>
      cases h₂ with
      | WhileFalse hf =>
          rw [ht] at hf
          exact absurd hf (by decide)
      | WhileTrue _ h₂₁ h₂₂ =>
          have hs := ih₁ h₂₁
          subst hs
          exact ih₂ h₂₂
