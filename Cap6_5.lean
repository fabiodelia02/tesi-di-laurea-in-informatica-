import Tesi.Cap6_4


-- 6.5 — Un Un controllore eseguibile per la sicurezza
-- ===========================================================
--
-- SecTyping sec l c è una relazione in Prop: è adatta alle prove,
-- ma non è eseguibile direttamente.
--
-- okLevel è la controparte calcolabile di SecTyping: restituisce true
-- esattamente quando il comando è tipabile rispetto alla politica sec
-- e al livello di contesto l.
--
-- La funzione non esegue c su uno stato concreto: percorre invece la
-- struttura del comando nel dominio astratto dei livelli di sicurezza.


def okLevel (sec : SecEnv) : Level → Com → Bool

  -- Skip non modifica lo stato: è sempre sicuro.
  | _, Com.Skip =>
      true

  -- L'assegnamento è sicuro se il valore assegnato e il contesto
  -- corrente non hanno un livello maggiore della variabile x.
  | l, Com.Assign x a =>
      Level.le (secA sec a) (sec x) &&
      Level.le l (sec x)

  -- Entrambi i comandi della sequenza devono essere sicuri
  -- nello stesso contesto.
  | l, Com.Seq c1 c2 =>
      okLevel sec l c1 &&
      okLevel sec l c2

  -- I rami del condizionale vengono controllati nel contesto
  -- innalzato dal livello della guardia.
  | l, Com.If b c1 c2 =>
      let lCtx := Level.join l (secB sec b)
      okLevel sec lCtx c1 &&
      okLevel sec lCtx c2

  -- Il corpo del ciclo viene controllato nel contesto innalzato
  -- dal livello della guardia.
  | l, Com.While b c =>
      let lCtx := Level.join l (secB sec b)
      okLevel sec lCtx c


-- Esempi con secAllLow
-- ===========================================================
--
-- Tutte le variabili sono Low, quindi non possono esistere
-- flussi da High verso Low.


-- Una costante Low assegnata a una variabile Low è accettata.
example :
    okLevel secAllLow Level.Low
      (Com.Assign "x" (Aexp.N 0)) = true := by
  decide


-- Una guardia e due assegnamenti pubblici sono accettati.
example :
    okLevel secAllLow Level.Low
      (Com.If (Bexp.Less (Aexp.V "x") (Aexp.N 1))
        (Com.Assign "y" (Aexp.N 0))
        (Com.Assign "y" (Aexp.N 1))) = true := by
  decide


-- Esempi con secExample
-- ===========================================================
--
-- "h" è High; tutte le altre variabili sono Low.


-- Incremento di una variabile pubblica:
-- il comando non dipende da informazioni riservate.
def publicIncrement : Com :=
  Com.Assign "x" (Aexp.Plus (Aexp.V "x") (Aexp.N 1))

example : okLevel secExample Level.Low publicIncrement = true := by
  decide


-- Flusso esplicito:
-- il valore segreto di "h" viene copiato nella variabile pubblica "x".
def explicitLeak : Com :=
  Com.Assign "x" (Aexp.V "h")

example : okLevel secExample Level.Low explicitLeak = false := by
  decide


-- Flusso implicito:
-- la guardia dipende da "h", ma i due rami modificano "x".
def implicitLeak : Com :=
  Com.If (Bexp.Less (Aexp.N 0) (Aexp.V "h"))
    (Com.Assign "x" (Aexp.N 0))
    (Com.Assign "x" (Aexp.N 1))

example : okLevel secExample Level.Low implicitLeak = false := by
  decide


-- Aggiornamento riservato:
-- "h" influenza soltanto la stessa variabile High.
def secretUpdate : Com :=
  Com.Assign "h" (Aexp.Plus (Aexp.V "h") (Aexp.N 1))

example : okLevel secExample Level.Low secretUpdate = true := by
  decide


-- Ciclo non sicuro:
-- la guardia dipende da "h" e il corpo aggiorna la variabile Low "x".
def unsafeLoop : Com :=
  Com.While (Bexp.Less (Aexp.N 0) (Aexp.V "h"))
    (Com.Assign "x" (Aexp.Plus (Aexp.V "x") (Aexp.N 1)))

example : okLevel secExample Level.Low unsafeLoop = false := by
  decide
