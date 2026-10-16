import Tesi.Cap6_3


-- 6.4 — Il sistema di tipi di sicurezza


-- SecTyping sec l c significa:
-- il comando c è sicuro rispetto alla politica sec quando viene
-- eseguito in un contesto di livello l. Il giudizio impedisce sia flussi espliciti,
-- controllando i valori assegnati alle variabili, sia flussi impliciti,
-- innalzando il livello del contesto nei rami condizionali e nei cicli.
inductive SecTyping : SecEnv → Level → Com → Prop where

  -- Skip non modifica alcuna variabile: è sicuro a ogni livello.
  | Skip {sec : SecEnv} {l : Level} :
      SecTyping sec l Com.Skip

  -- Per un assegnamento devono valere due condizioni:
  -- 1. il livello dell'espressione non supera quello della variabile;
  -- 2. il livello del contesto non supera quello della variabile.
  | Assign {sec : SecEnv} {l : Level} {x : Vname} {a : Aexp} :
      Level.le (secA sec a) (sec x) = true →
      Level.le l (sec x) = true →
      SecTyping sec l (Com.Assign x a)

  -- Una sequenza è sicura se entrambi i comandi sono sicuri nello stesso contesto di sicurezza.
  | Seq {sec : SecEnv} {l : Level} {c1 c2 : Com} :
      SecTyping sec l c1 →
      SecTyping sec l c2 →
      SecTyping sec l (Com.Seq c1 c2)

  -- Nei due rami di un condizionale il contesto viene innalzato
  -- con il livello della guardia, per evitare flussi impliciti.
  | If {sec : SecEnv} {l : Level} {b : Bexp} {c1 c2 : Com} :
      SecTyping sec (Level.join l (secB sec b)) c1 →
      SecTyping sec (Level.join l (secB sec b)) c2 →
      SecTyping sec l (Com.If b c1 c2)

  -- Nel corpo del ciclo il contesto viene innalzato con il livello della guardia del ciclo.
  | While {sec : SecEnv} {l : Level} {b : Bexp} {c : Com} :
      SecTyping sec (Level.join l (secB sec b)) c →
      SecTyping sec l (Com.While b c)


-- Notazione compatta per il giudizio di tipizzazione:
-- ⊢[sec] l : c  significa SecTyping sec l c.
notation:55 "⊢[" sec "]" l ":" c => SecTyping sec l c


-- Lemmi ausiliari sull'ordine e sul join.

-- Transitività dell'ordine:
-- se l1 <= l2 e l2 <= l3, allora l1 <= l3.
theorem Level.le_trans {l1 l2 l3 : Level} :
    Level.le l1 l2 = true →
    Level.le l2 l3 = true →
    Level.le l1 l3 = true := by
  cases l1 <;> cases l2 <;> cases l3 <;> simp_all [Level.le]


-- Monotonicità del join rispetto al primo argomento:
-- se lLow <= l, allora join lLow k <= join l k.
theorem Level.join_mono_left {l lLow k : Level} :
    Level.le lLow l = true →
    Level.le (Level.join lLow k) (Level.join l k) = true := by
  cases l <;> cases lLow <;> cases k <;> simp_all [Level.le, Level.join]


-- Esempio limite: con secAllLow tutte le variabili sono pubbliche.
-- Assegnare la costante 0 alla variabile pubblica "x" è sicuro.
example : SecTyping secAllLow Level.Low (Com.Assign "x" (Aexp.N 0)) :=
  SecTyping.Assign
    (by simp [secA, Level.le])
    (by simp [Level.le])


-- Esempio con secExample: "h" è riservata, mentre "x" è pubblica.
-- L'assegnamento di una costante a "x" resta sicuro.
example : SecTyping secExample Level.Low (Com.Assign "x" (Aexp.N 0)) :=
  SecTyping.Assign
    (by simp [secA, Level.le])
    (by simp [Level.le])


-- Anti-monotonicità nel livello del contesto:
-- se c è sicuro al livello l, allora è sicuro anche a ogni livello
-- lLow <= l, cioè in un contesto meno riservato.
theorem secTyping_antimono {sec : SecEnv} {c : Com} {l lLow : Level} :
    SecTyping sec l c →
    Level.le lLow l = true →
    SecTyping sec lLow c := by

  intro hTyping
  induction hTyping generalizing lLow with

  -- Skip è sicuro a ogni livello, quindi non serve usare l'ipotesi.
  | Skip =>
      intro _
      exact SecTyping.Skip

  -- Il vincolo sul flusso esplicito non dipende dal contesto.
  -- Per il vincolo sul contesto si usa la transitività:
  -- lLow <= l e l <= sec x implicano lLow <= sec x.
  | Assign hEsp hCtx =>
      intro hLow
      exact SecTyping.Assign hEsp (Level.le_trans hLow hCtx)

  -- Le due ipotesi induttive trasferiscono la sicurezza dei due
  -- sottocomandi dal contesto l al contesto lLow.
  | Seq hLeft hRight ihLeft ihRight =>
      intro hLow
      exact SecTyping.Seq (ihLeft hLow) (ihRight hLow)

  -- Entrambi i rami sono tipati al livello join l (secB sec b).
  -- La monotonicità del join permette di passare al nuovo livello
  -- join lLow (secB sec b), applicando poi le ipotesi induttive.
  | If hThen hElse ihThen ihElse =>
      intro hLow
      exact SecTyping.If
        (ihThen (Level.join_mono_left hLow))
        (ihElse (Level.join_mono_left hLow))

  -- Il ragionamento è identico al caso If, ma riguarda il corpo
  -- del ciclo invece dei due rami del condizionale.
  | While hBody ihBody =>
      intro hLow
      exact SecTyping.While
        (ihBody (Level.join_mono_left hLow))
