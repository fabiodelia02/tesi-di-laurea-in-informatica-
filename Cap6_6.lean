-- Cap6_6.lean — Dimostrazione della non interferenza
-- ===========================================================
-- Obiettivo: dimostrare che programmi tipati con SecTyping non permettono
-- flussi di informazione da dati High a osservatori Low.
--
-- Strategia:
--   1. okLevel ↔ SecTyping (corrispondenza interprete/tipi)
--   2. lowEq (stati indistinguibili a livello l)
--   3. Lemmi su Level (proprietà tecniche)
--   4. Espressioni non interferenti (aexp, bexp)
--   5. Confinamento (comandi a livello non osservabile non modificano Low)
--   6. Teorema principale (noninterference)

import Tesi.Cap6_5


-- =============================================================================
-- 1. CORRISPONDENZA: okLevel ↔ SecTyping
-- =============================================================================

/-- okLevel restituisce true esattamente quando SecTyping è derivabile -/
theorem okLevel_iff_secTyping
    (sec : SecEnv) (l : Level) (c : Com) :
    okLevel sec l c = true ↔ SecTyping sec l c := by
  induction c generalizing l with

  | Skip =>
      -- Skip: sempre sicuro, nessuna azione
      constructor
      · intro _; exact SecTyping.Skip           -- true → derivazione
      · intro _; rfl                            -- derivazione → true

  | Assign x a =>
      -- Assign: due condizioni (espressione e contesto)
      constructor
      · intro h                                 -- okLevel = true
        simp [okLevel] at h                     -- estrai le due condizioni
        exact SecTyping.Assign h.1 h.2          -- costruisci derivazione
      · intro h                                 -- SecTyping derivabile
        cases h with
        | Assign hExpr hCtx =>                  -- estrai premesse
            simp [okLevel, hExpr, hCtx]         -- verifica okLevel = true

  | Seq c1 c2 ih1 ih2 =>
      -- Seq: entrambi i comandi devono essere sicuri
      constructor
      · intro h                                 -- okLevel = true
        have hBoth : okLevel sec l c1 = true ∧ okLevel sec l c2 = true := by
          simpa [okLevel] using h               -- separa le due condizioni
        -- applica ipotesi induttive a ciascun comando
        exact SecTyping.Seq ((ih1 l).mp hBoth.1) ((ih2 l).mp hBoth.2)
      · intro h                                 -- SecTyping.Seq
        cases h with
        | Seq hFirst hSecond =>                 -- estrai le due derivazioni
          -- applica ipotesi induttive inverse
          have hFirstOk : okLevel sec l c1 = true := (ih1 l).mpr hFirst
          have hSecondOk : okLevel sec l c2 = true := (ih2 l).mpr hSecond
          simp [okLevel, hFirstOk, hSecondOk]   -- ricomponi okLevel

  | If b c1 c2 ih1 ih2 =>
      -- If: rami controllati nel contesto innalzato dalla guardia
      constructor
      · intro h                                 -- okLevel = true
        let lCtx := Level.join l (secB sec b)   -- contesto innalzato
        have hBoth : okLevel sec lCtx c1 = true ∧ okLevel sec lCtx c2 = true := by
          simpa [okLevel, lCtx] using h         -- estrai condizioni sui rami
        -- applica ipotesi induttive nel contesto innalzato
        exact SecTyping.If ((ih1 lCtx).mp hBoth.1) ((ih2 lCtx).mp hBoth.2)
      · intro h                                 -- SecTyping.If
        cases h with
        | If hThen hElse =>                     -- estrai derivazioni dei rami
          let lCtx := Level.join l (secB sec b) -- contesto innalzato
          -- applica ipotesi induttive inverse
          have hThenOk : okLevel sec lCtx c1 = true := (ih1 lCtx).mpr hThen
          have hElseOk : okLevel sec lCtx c2 = true := (ih2 lCtx).mpr hElse
          simp [okLevel, lCtx, hThenOk, hElseOk]

  | While b c ih =>
      -- While: corpo controllato nel contesto innalzato
      constructor
      · intro h                                 -- okLevel = true
        let lCtx := Level.join l (secB sec b)   -- contesto innalzato
        have hBodyOk : okLevel sec lCtx c = true := by
          simpa [okLevel, lCtx] using h         -- estrai condizione sul corpo
        exact SecTyping.While ((ih lCtx).mp hBodyOk)
      · intro h                                 -- SecTyping.While
        cases h with
        | While hBody =>                        -- estrai derivazione del corpo
          let lCtx := Level.join l (secB sec b) -- contesto innalzato
          have hBodyOk : okLevel sec lCtx c = true := (ih lCtx).mpr hBody
          simp [okLevel, lCtx, hBodyOk]         -- ricomponi okLevel


-- =============================================================================
-- 2. INDISTINGUIBILITÀ (lowEq)
-- =============================================================================

/-- Due stati sono indistinguibili a livello l se coincidono su tutte le
    variabili con livello ≤ l (variabili osservabili da un utente Low) -/
def lowEq (sec : SecEnv) (l : Level) (s1 s2 : State) : Prop :=
  ∀ x : Vname, Level.le (sec x) l = true → s1 x = s2 x

notation:50 s1 " ≈[" sec ", " l "] " s2 => lowEq sec l s1 s2

-- lowEq è una relazione di equivalenza
theorem lowEq_refl {sec : SecEnv} {l : Level} {s : State} : s ≈[sec, l] s := by
  intro x _; rfl  -- ogni stato è uguale a se stesso

theorem lowEq_symm {sec : SecEnv} {l : Level} {s1 s2 : State} :
    (s1 ≈[sec, l] s2) → (s2 ≈[sec, l] s1) := by
  intro h x hx; exact (h x hx).symm  -- simmetria dell'uguaglianza

theorem lowEq_trans {sec : SecEnv} {l : Level} {s1 s2 s3 : State} :
    (s1 ≈[sec, l] s2) → (s2 ≈[sec, l] s3) → (s1 ≈[sec, l] s3) := by
  intro h12 h23 x hx; exact (h12 x hx).trans (h23 x hx)  -- transitività


-- =============================================================================
-- 3. LEMMI SU LEVEL
-- =============================================================================

/-- Se max(a,b) ≤ l, allora anche a ≤ l -/
theorem Level.le_of_join_le_left {a b l : Level} :
    Level.le (Level.join a b) l = true → Level.le a l = true := by
  cases a <;> cases b <;> cases l <;> simp_all [Level.join, Level.le]

/-- Se max(a,b) ≤ l, allora anche b ≤ l -/
theorem Level.le_of_join_le_right {a b l : Level} :
    Level.le (Level.join a b) l = true → Level.le b l = true := by
  cases a <;> cases b <;> cases l <;> simp_all [Level.join, Level.le]

/-- Se k ≤ l, allora max(l,k) = l (assorbimento) -/
theorem Level.join_eq_left_of_le {l k : Level} :
    Level.le k l = true → Level.join l k = l := by
  cases l <;> cases k <;> simp_all [Level.le, Level.join]

/-- Se k ≰ l (guardia non osservabile), allora max(l,k) ≰ l -/
theorem Level.join_not_le_of_guard_not_le {l k : Level} :
    Level.le k l = false → Level.le (Level.join l k) l = false := by
  cases l <;> cases k <;> simp_all [Level.le, Level.join]

/-- Se lBase ≰ l, allora max(lBase,k) ≰ l -/
theorem Level.join_not_le_of_base_not_le {lBase l k : Level} :
    Level.le lBase l = false → Level.le (Level.join lBase k) l = false := by
  cases lBase <;> cases l <;> cases k <;> simp_all [Level.le, Level.join]


-- =============================================================================
-- 4. NON INTERFERENZA PER ESPRESSIONI
-- =============================================================================

/-- Un'espressione aritmetica con livello ≤ l assume lo stesso valore
    in stati indistinguibili a livello l -/
theorem noninterference_aexp {sec : SecEnv} {l : Level} {s1 s2 : State}
    {a : Aexp}
    (hle : Level.le (secA sec a) l = true)   -- livello(a) ≤ l
    (heq : s1 ≈[sec, l] s2) :                -- stati indistinguibili
    aval a s1 = aval a s2 := by              -- stesso valore
  induction a with
  | N n =>
      rfl                                    -- costante: sempre uguale
  | V x =>
      exact heq x hle                        -- variabile: usa lowEq
  | Plus a1 a2 ih1 ih2 =>
      -- livello(Plus a1 a2) = max(livello(a1), livello(a2)) ≤ l
      have hle1 : Level.le (secA sec a1) l = true :=
        Level.le_of_join_le_left (a := secA sec a1) (b := secA sec a2) hle
      have hle2 : Level.le (secA sec a2) l = true :=
        Level.le_of_join_le_right (a := secA sec a1) (b := secA sec a2) hle
      -- applica ipotesi induttive ai sotto-termini
      simp [aval, ih1 hle1, ih2 hle2]

/-- Un'espressione booleana con livello ≤ l ha lo stesso valore
    in stati indistinguibili a livello l -/
theorem noninterference_bexp {sec : SecEnv} {l : Level} {s1 s2 : State}
    {b : Bexp}
    (hle : Level.le (secB sec b) l = true)   -- livello(b) ≤ l
    (heq : s1 ≈[sec, l] s2) :                -- stati indistinguibili
    bval b s1 = bval b s2 := by              -- stesso valore booleano
  induction b with
  | Bc v =>
      rfl                                    -- costante: sempre uguale
  | Not b ih =>
      simp [bval, ih hle]                    -- usa ipotesi su b
  | And b1 b2 ih1 ih2 =>
      -- livello(And b1 b2) = max(livello(b1), livello(b2)) ≤ l
      have hle1 : Level.le (secB sec b1) l = true :=
        Level.le_of_join_le_left (a := secB sec b1) (b := secB sec b2) hle
      have hle2 : Level.le (secB sec b2) l = true :=
        Level.le_of_join_le_right (a := secB sec b1) (b := secB sec b2) hle
      simp [bval, ih1 hle1, ih2 hle2]
  | Less a1 a2 =>
      -- livello(Less a1 a2) = max(livello(a1), livello(a2)) ≤ l
      have hle1 : Level.le (secA sec a1) l = true :=
        Level.le_of_join_le_left (a := secA sec a1) (b := secA sec a2) hle
      have hle2 : Level.le (secA sec a2) l = true :=
        Level.le_of_join_le_right (a := secA sec a1) (b := secA sec a2) hle
      -- applica noninterference_aexp alle sotto-espressioni
      simp [bval, noninterference_aexp hle1 heq, noninterference_aexp hle2 heq]


-- =============================================================================
-- 5. CONFINAMENTO
-- =============================================================================

/-- Se un comando è tipato a livello lCtx ≰ l, allora la sua esecuzione
    non modifica le variabili osservabili a l (quelle con sec(x) ≤ l) -/
theorem confinement {sec : SecEnv} {c : Com} {s t : State}
    {l lCtx : Level}
    (hty : SecTyping sec lCtx c)              -- comando tipato a lCtx
    (hstep : c / s ==> t)                     -- esecuzione: s → t
    (hNotObs : Level.le lCtx l = false) :     -- lCtx non osservabile da l
    ∀ x : Vname, Level.le (sec x) l = true → s x = t x := by  -- s,t uguali su Low
  induction hstep generalizing lCtx with
  | Skip =>
      intro x _; rfl                          -- Skip non modifica nulla

  | @Assign x' a' s'' =>
      -- Assegnamento: modifica solo x', ma x' ha livello > l
      cases hty with
      | Assign _ hCtx =>                      -- hCtx: livello(a') ≤ sec(x')
          intro y hy                          -- y osservabile (sec(y) ≤ l)
          show s'' y = upd s'' x' (aval a' s'') y
          simp only [upd]
          by_cases hxy : y = x'
          · -- y = x': assurdo, perché sec(x') ≥ lCtx > l
            exfalso
            rw [hxy] at hy
            have hChain : Level.le lCtx l = true := Level.le_trans hCtx hy
            rw [hNotObs] at hChain            -- contraddizione
            exact absurd hChain (by decide)
          · -- y ≠ x': upd non modifica y
            simp [hxy]

  | @Seq c1' c2' s1' s2' s3' h1' h2' ih1 ih2 =>
      -- Sequenza: applica confinamento a entrambi i comandi
      cases hty with
      | Seq hty1 hty2 =>
          intro x hx
          -- s1' ≈ s2' su Low (primo comando)
          -- s2' ≈ s3' su Low (secondo comando)
          exact (ih1 hty1 hNotObs x hx).trans (ih2 hty2 hNotObs x hx)

  | @IfTrue b' c1' c2' s' t' hb' hstep' ih =>
      -- IfTrue: c1 eseguito nel contesto innalzato
      cases hty with
      | If hty1 _ =>
          intro x hx
          -- contesto innalzato: join(lCtx, livello(b')) ≰ l
          have hNotObsCtx : Level.le (Level.join lCtx (secB sec b')) l = false :=
            Level.join_not_le_of_base_not_le hNotObs
          -- applica ipotesi induttiva a c1
          exact ih hty1 hNotObsCtx x hx

  | @IfFalse b' c1' c2' s' t' hb' hstep' ih =>
      -- IfFalse: c2 eseguito nel contesto innalzato
      cases hty with
      | If _ hty2 =>
          intro x hx
          have hNotObsCtx : Level.le (Level.join lCtx (secB sec b')) l = false :=
            Level.join_not_le_of_base_not_le hNotObs
          -- applica ipotesi induttiva a c2
          exact ih hty2 hNotObsCtx x hx

  | @WhileFalse b' c' s' hb' =>
      -- WhileFalse: nessuna esecuzione, stato invariato
      intro x _; rfl

  | @WhileTrue b' c' s1' s2' s3' hb' h1' h2' ih1 ih2 =>
      -- WhileTrue: c eseguito più volte
      cases hty with
      | While htyBody =>
          intro x hx
          -- contesto innalzato per il corpo: join(lCtx, livello(b')) ≰ l
          have hNotObsCtx : Level.le (Level.join lCtx (secB sec b')) l = false :=
            Level.join_not_le_of_base_not_le hNotObs
          -- s1' ≈ s2' su Low (prima iterazione del corpo)
          have hMid := ih1 htyBody hNotObsCtx x hx
          -- s2' ≈ s3' su Low (iterazioni restanti)
          have hEnd := ih2 (SecTyping.While htyBody) hNotObs x hx
          exact hMid.trans hEnd               -- transitività


/-- Se la guardia di un ciclo non è osservabile, il ciclo non modifica
    le variabili osservabili a l -/
theorem while_confined {sec : SecEnv} {l : Level}
    {b : Bexp} {cbody : Com} {s t : State}
    (htyBody : SecTyping sec (Level.join l (secB sec b)) cbody)
    (hNotObs : Level.le (Level.join l (secB sec b)) l = false)
    (hstep : Com.While b cbody / s ==> t) :
    s ≈[sec, l] t := by                       -- stato finale ≈ stato iniziale
  generalize hc : Com.While b cbody = c at hstep
  induction hstep generalizing b cbody with
  | Skip => cases hc                          -- caso impossibile
  | Assign => cases hc                        -- caso impossibile
  | Seq _ _ _ _ => cases hc                   -- caso impossibile
  | IfTrue _ _ _ => cases hc                  -- caso impossibile
  | IfFalse _ _ _ => cases hc                 -- caso impossibile
  | @WhileFalse b' c' s' hb' =>
      -- Ciclo che termina subito: stato invariato
      cases hc; exact lowEq_refl
  | @WhileTrue b' c' s1' s2' s3' hb' hbody hrest ihbody ihrest =>
      -- WhileTrue: corpo eseguito, poi ciclo continua
      cases hc
      -- s1' ≈ s2' su Low (confinamento del corpo)
      have hBodyConf : s1' ≈[sec, l] s2' :=
        confinement htyBody hbody hNotObs
      -- s2' ≈ s3' su Low (iterazioni restanti, per ipotesi induttiva)
      have hRestConf : s2' ≈[sec, l] s3' :=
        ihrest htyBody hNotObs rfl
      exact lowEq_trans hBodyConf hRestConf   -- transitività


-- =============================================================================
-- 6. TEOREMA PRINCIPALE: NON INTERFERENZA
-- =============================================================================

/-- Se due stati iniziali sono indistinguibili a livello l e il comando è
    tipato a livello l, allora le due esecuzioni terminanti producono stati
    finali ancora indistinguibili a l -/
theorem noninterference {sec : SecEnv} {c : Com} {l : Level}
    {s1 s2 t1 t2 : State}
    (hty : SecTyping sec l c)                 -- comando sicuro a livello l
    (heq : s1 ≈[sec, l] s2)                   -- stati iniziali ≈
    (h1 : c / s1 ==> t1)                      -- esecuzione 1: s1 → t1
    (h2 : c / s2 ==> t2)                      -- esecuzione 2: s2 → t2
    : t1 ≈[sec, l] t2 := by                   -- stati finali ≈
  induction h1 generalizing l s2 t2 with

  | Skip =>
      -- Skip: stati invariati, usa lowEq iniziale
      cases h2 with
      | Skip => exact heq

  | @Assign x' a' s1'' =>
      -- Assign: modifica solo x', ma x' ha livello > l
      cases h2 with
      | Assign =>
          cases hty with
          | Assign hleA hleX =>               -- hleA: livello(a') ≤ sec(x')
              intro y hy                      -- y osservabile (sec(y) ≤ l)
              simp only [upd]
              by_cases hxy : y = x'
              · -- y = x': assurdo, perché sec(x') ≥ l > l
                subst hxy
                simp only [if_pos]
                -- a' ha stesso valore in s1 e s2 (noninterference_aexp)
                exact noninterference_aexp (Level.le_trans hleA hy) heq
              · -- y ≠ x': upd non modifica y
                simp only [hxy, if_false]
                exact heq y hy

  | @Seq c1' c2' s1a s1b s1c h1a h1b ih1a ih1b =>
      -- Seq: applica noninterference a ciascun comando
      cases h2 with
      | Seq h2a h2b =>
          cases hty with
          | Seq hty1 hty2 =>
              -- s1a ≈ s2a su Low (stati iniziali)
              -- c1: s1a → s1b, c1: s2a → s2b
              have hMid := ih1a hty1 heq h2a  -- s1b ≈ s2b
              -- c2: s1b → s1c, c2: s2b → s2c
              exact ih1b hty2 hMid h2b        -- s1c ≈ s2c

  | @IfTrue b' c1' c2' s1' t1' hb1 h1c ih =>
      -- IfTrue: b' vero in s1', c1 eseguito
      cases hty with
      | If hty1 hty2 =>
          by_cases hsb : Level.le (secB sec b') l = true
          · -- Caso 1: guardia osservabile (livello(b') ≤ l)
            -- Le due esecuzioni scelgono lo stesso ramo
            have heqlvl : Level.join l (secB sec b') = l :=
              Level.join_eq_left_of_le hsb    -- join(l, livello(b')) = l
            rw [heqlvl] at hty1               -- c1 tipato a livello l
            -- b' ha stesso valore in s1' e s2' (noninterference_bexp)
            have hb2 : bval b' s2 = true := by
              rw [← noninterference_bexp hsb heq]; exact hb1
            cases h2 with
            | IfTrue _ h2c =>
                -- Anche s2 esegue c1: applica ipotesi induttiva
                exact ih hty1 heq h2c
            | IfFalse hb2f _ =>
                -- Assurdo: b' non può essere vero e falso
                rw [hb2] at hb2f
                exact absurd hb2f (by decide)
          · -- Caso 2: guardia non osservabile (livello(b') ≰ l)
            -- I rami possono differire, ma non modificano Low
            have hnb : Level.le (secB sec b') l = false := by simpa using hsb
            have hNotObsCtx : Level.le (Level.join l (secB sec b')) l = false :=
              Level.join_not_le_of_guard_not_le hnb
            cases h2 with
            | IfTrue _ h2c =>
                -- s1' esegue c1, s2' esegue c1: entrambi confinati
                have hConf1 := confinement hty1 h1c hNotObsCtx
                have hConf2 := confinement hty1 h2c hNotObsCtx
                intro y hy
                -- s1' ≈ t1' su Low, s2' ≈ t2' su Low
                rw [← hConf1 y hy, ← hConf2 y hy]
                exact heq y hy                -- s1' ≈ s2' su Low
            | IfFalse _ h2c =>
                -- s1' esegue c1, s2' esegue c2: entrambi confinati
                have hConf1 := confinement hty1 h1c hNotObsCtx
                have hConf2 := confinement hty2 h2c hNotObsCtx
                intro y hy
                rw [← hConf1 y hy, ← hConf2 y hy]
                exact heq y hy

  | @IfFalse b' c1' c2' s1' t1' hb1 h1c ih =>
      -- IfFalse: b' falso in s1', c2 eseguito
      cases hty with
      | If hty1 hty2 =>
          by_cases hsb : Level.le (secB sec b') l = true
          · -- Caso 1: guardia osservabile
            have heqlvl : Level.join l (secB sec b') = l :=
              Level.join_eq_left_of_le hsb
            rw [heqlvl] at hty2               -- c2 tipato a livello l
            have hb2 : bval b' s2 = false := by
              rw [← noninterference_bexp hsb heq]; exact hb1
            cases h2 with
            | IfFalse _ h2c =>
                -- Anche s2 esegue c2
                exact ih hty2 heq h2c
            | IfTrue hb2t _ =>
                -- Assurdo: b' non può essere falso e vero
                rw [hb2] at hb2t
                exact absurd hb2t (by decide)
          · -- Caso 2: guardia non osservabile
            have hnb : Level.le (secB sec b') l = false := by simpa using hsb
            have hNotObsCtx : Level.le (Level.join l (secB sec b')) l = false :=
              Level.join_not_le_of_guard_not_le hnb
            cases h2 with
            | IfTrue _ h2c =>
                -- s1' esegue c2, s2' esegue c1: entrambi confinati
                have hConf1 := confinement hty2 h1c hNotObsCtx
                have hConf2 := confinement hty1 h2c hNotObsCtx
                intro y hy
                rw [← hConf1 y hy, ← hConf2 y hy]
                exact heq y hy
            | IfFalse _ h2c =>
                -- s1' esegue c2, s2' esegue c2: entrambi confinati
                have hConf1 := confinement hty2 h1c hNotObsCtx
                have hConf2 := confinement hty2 h2c hNotObsCtx
                intro y hy
                rw [← hConf1 y hy, ← hConf2 y hy]
                exact heq y hy

  | @WhileFalse b' c' s1' hb1 =>
      -- WhileFalse: ciclo termina subito
      cases hty with
      | While htyBody =>
          by_cases hsb : Level.le (secB sec b') l = true
          · -- Guardia osservabile: anche s2 termina subito
            have hb2 : bval b' s2 = false := by
              rw [← noninterference_bexp hsb heq]; exact hb1
            cases h2 with
            | WhileFalse _ => exact heq       -- stati invariati
            | WhileTrue hb2t _ _ =>
                -- Assurdo: b' non può essere falso e vero
                rw [hb2] at hb2t
                exact absurd hb2t (by decide)
          · -- Guardia non osservabile: ciclo confinato
            have hnb : Level.le (secB sec b') l = false := by simpa using hsb
            have hNotObsCtx : Level.le (Level.join l (secB sec b')) l = false :=
              Level.join_not_le_of_guard_not_le hnb
            -- s2 ≈ t2 su Low (while_confined)
            have hConf2 : s2 ≈[sec, l] t2 :=
              while_confined htyBody hNotObsCtx h2
            exact lowEq_trans heq hConf2      -- s1 ≈ s2 ≈ t2

  | @WhileTrue b' c' s1a s1b s1c hb1 h1a h1b ih1a ih1b =>
      -- WhileTrue: ciclo esegue almeno un'iterazione
      cases hty with
      | While htyBody =>
          by_cases hsb : Level.le (secB sec b') l = true
          · -- Caso 1: guardia osservabile
            -- Le due esecuzioni fanno lo stesso numero di iterazioni
            have heqlvl : Level.join l (secB sec b') = l :=
              Level.join_eq_left_of_le hsb
            have htyBodyAtL : SecTyping sec l c' := heqlvl ▸ htyBody
            have hb2 : bval b' s2 = true := by
              rw [← noninterference_bexp hsb heq]; exact hb1
            cases h2 with
            | WhileTrue _ h2a h2b =>
                -- s1a → s1b (c'), s2a → s2b (c')
                have hMid := ih1a htyBodyAtL heq h2a  -- s1b ≈ s2b
                -- s1b → s1c (While), s2b → s2c (While)
                have htyWhile : SecTyping sec l (Com.While b' c') :=
                  SecTyping.While htyBody
                exact ih1b htyWhile hMid h2b
            | WhileFalse hb2f =>
                -- Assurdo: b' non può essere vero e falso
                rw [hb2] at hb2f
                exact absurd hb2f (by decide)
          · -- Caso 2: guardia non osservabile
            -- Entrambi i cicli sono confinati
            have hnb : Level.le (secB sec b') l = false := by simpa using hsb
            have hNotObsCtx : Level.le (Level.join l (secB sec b')) l = false :=
              Level.join_not_le_of_guard_not_le hnb
            -- s1a ≈ s1c su Low (ciclo completo confinato)
            have hWhole1 : Com.While b' c' / s1a ==> s1c :=
              BigStep.WhileTrue hb1 h1a h1b
            have hConf1 : s1a ≈[sec, l] s1c :=
              while_confined htyBody hNotObsCtx hWhole1
            -- s2 ≈ t2 su Low (ciclo confinato)
            have hConf2 : s2 ≈[sec, l] t2 :=
              while_confined htyBody hNotObsCtx h2
            -- s1a ≈ s2 ≈ t2
            have hS1aT2 : s1a ≈[sec, l] t2 := lowEq_trans heq hConf2
            -- s1c ≈ s1a (simmetria)
            have hS1cS1a : s1c ≈[sec, l] s1a := lowEq_symm hConf1
            exact lowEq_trans hS1cS1a hS1aT2  -- s1c ≈ s1a ≈ t2
