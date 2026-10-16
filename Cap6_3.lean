import Tesi.Cap6_1_2


-- 6.3 — Livelli di sicurezza delle variabili


-- Un livello indica quanto un dato sia osservabile.
-- Low: informazione pubblica.
-- High: informazione riservata.
inductive Level where
  | Low  : Level
  | High : Level
deriving Repr, DecidableEq


-- Ordinamento dei livelli di sicurezza.
-- Low può fluire sia verso Low sia verso High.
-- High può fluire soltanto verso High.
def Level.le : Level → Level → Bool
  | Level.Low,  _          => true
  | Level.High, Level.High => true
  | Level.High, Level.Low  => false


-- Permette di usare la notazione l1 <= l2 per i livelli.
-- L'ordine vale quando Level.le restituisce true.
instance : LE Level := ⟨fun l1 l2 => Level.le l1 l2 = true⟩


-- Join, cioè il massimo tra due livelli.
-- Se almeno uno dei due livelli è High, il risultato è High.
def Level.join : Level → Level → Level
  | Level.High, _ => Level.High
  | _, Level.High => Level.High
  | _, _          => Level.Low


-- Politica di sicurezza:
-- associa staticamente a ogni nome di variabile il suo livello.
abbrev SecEnv := Vname → Level


-- Livello di sicurezza di un'espressione aritmetica.
-- Una costante è pubblica; una variabile assume il livello
-- assegnato dalla politica; una somma usa il massimo dei livelli.
def secA (sec : SecEnv) : Aexp → Level
  | Aexp.N _        => Level.Low
  | Aexp.V x        => sec x
  | Aexp.Plus a1 a2 =>
      Level.join (secA sec a1) (secA sec a2)


-- Livello di sicurezza di un'espressione booleana.
-- Le costanti sono pubbliche; negazione e congiunzione propagano
-- il livello delle sottoespressioni; il confronto dipende dagli
-- operandi aritmetici.
def secB (sec : SecEnv) : Bexp → Level
  | Bexp.Bc _       => Level.Low
  | Bexp.Not b      => secB sec b
  | Bexp.And b1 b2  => Level.join (secB sec b1) (secB sec b2)
  | Bexp.Less a1 a2 => Level.join (secA sec a1) (secA sec a2)


-- Politica limite: ogni variabile è pubblica.
-- È utile per verificare esempi senza dati riservati.
def secAllLow : SecEnv :=
  fun _ => Level.Low


-- Politica di esempio:
-- "h" rappresenta un dato riservato, tutte le altre variabili
-- sono considerate pubbliche.
def secExample : SecEnv :=
  fun x => if x = "h" then Level.High else Level.Low
