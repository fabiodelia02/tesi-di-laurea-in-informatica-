-- Cap7.lean — Limiti della non interferenza formalizzata
-- ===========================================================
-- Questo file contiene il codice corrispondente al Capitolo 7.
--
-- In particolare, la Sezione 7.2 mostra che il sistema di tipi e il
-- controllore okLevel non impediscono l'uso della terminazione come
-- canale di informazione. Questo limite non dipende dall'implementazione
-- dell'analisi statica, ma dalla nozione di non interferenza
-- termination-insensitive garantita dal teorema noninterference.

import Tesi.Cap6_6


-- 7.2 — Il canale della terminazione
-- ===========================================================

/-- Ciclo che termina se e solo se il valore iniziale di "h" è
    diverso da zero.

    Poiché in Lean i valori sono numeri naturali, la guardia
    ¬(0 < h) è equivalente a h = 0. Se h = 0, la guardia resta
    sempre vera e il ciclo diverge; se h ≠ 0, la guardia è falsa
    e il ciclo termina immediatamente. -/
def leakByTermination : Com :=
  Com.While (Bexp.Not (Bexp.Less (Aexp.N 0) (Aexp.V "h")))
    Com.Skip


/-- Il comando è accettato dal controllore: il corpo è Skip, che è
    tipabile a qualunque livello di contesto, anche quando la guardia
    riservata innalza il contesto a High. -/
example :
    okLevel secExample Level.Low leakByTermination = true := by
  decide


/-- Per l'equivalenza dimostrata nella Sezione 6.6, il comando è anche
    derivabile nel giudizio induttivo SecTyping. Il teorema di non
    interferenza si applica quindi a leakByTermination; il suo limite
    riguarda le premesse, che richiedono che entrambe le esecuzioni
    confrontate terminino. -/
theorem leakByTermination_secTyping :
    SecTyping secExample Level.Low leakByTermination :=
  (okLevel_iff_secTyping secExample Level.Low leakByTermination).mp rfl
