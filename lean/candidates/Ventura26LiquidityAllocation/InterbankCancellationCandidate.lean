import Ventura26LiquidityAllocation.EconomicModel

/-!
# Cancelacion interbancaria del candidato literal: PROPUESTA SIN COMPILAR

Estado: CANDIDATO SIN COMPILAR. Este archivo no acredita una comprobacion Lean,
un cierre de axiomas ni una aprobacion semantica independiente.

Fuente del proyecto: alejandroventuraventurameza-tech/ai-project,
rama work/chat-continuity, commit 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base de AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Toolchain esperado: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado por el manifiesto: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Modulo propuesto: Ventura26LiquidityAllocation.InterbankCancellationCandidate.
Destino propuesto en la base reconstruida:
papers/Ventura26LiquidityAllocation/InterbankCancellationCandidate.lean.

No se modifica el checkpoint, su import raiz ni ninguna rama de GitHub.
El checkpoint no es un proyecto Lake autonomo. Este archivo requiere la base
fijada y los modulos conservados en los destinos de checkpoint_manifest.json.

Identidad de los modulos consultados, comprobada sobre los bytes recuperados:
EconomicModel.lean, SHA256:
d5e9bb95aad09ff515cc1418778c241d1b91ca3095c02b31eb369f496ea38d86
FinancialCore.lean, SHA256:
4130b338183b3e5e659df7a7f2f517fc356967404c2571a82cea0154f9fc58fa

## Argumento matematico y alcance

En una fecha e historia fijas, sean tau > 0, M > 0, RR > 0,
xi = RD / RR, rho < xi y r = localPrefixReserveDepositRatio P (d t) > 0.
Se exige que rho coincida con P.reserveRequirementPath t h.
La ley BinarySymmetricPaymentLaw tiene dos atomos distintos, pesos 1/2 y
realizaciones -zeta y +zeta, con zeta > 0. El lema existente del momento
absoluto da E|omega| = zeta.

Definicionalmente,
  r = rho + (xi-rho)*zeta*(1-tau)/(1+tau),
  D = M/r > 0,  M = r*D.
La ultima igualdad se deriva; no es una premisa nueva.
Con a = (xi-rho)*zeta*D > 0 y b = 2*a/(1+tau) > 0,
  s_minus = -tau*b < 0,  s_plus = b > 0.
Los agregados de deficit y excedente son -s_minus/2 y s_plus/2.
Por ello satisfacen BilateralOTCActivity, incluida la razon tau.
El lema existente otcMatchingFractions_clear iguala los dos volumenes
negociados. La esperanza del flujo individual, que es el promedio de sus
dos valores, queda igual a cero.

La identidad de matching cubre tau <= 1 y tau > 1, incluido tau = 1.
Esos casos OTC no son las ramas macroeconomicas S y B.
El enunciado conserva RR > 0 como condicion del dominio economico, aunque
el nucleo escalar de la cancelacion solo necesita el valor definido de xi.

El primer teorema de elevacion deriva la premisa hinterbank en todas las
historias admisibles y aplica localSlackLiteralAllocation_settlementClears.
No recibe como hipotesis clearing, un regimen OTC ni equilibrio completo.
La secuencia d sigue siendo un dato condicional. Los lemas posteriores
derivan la compatibilidad de encaje del arbol conservado y la positividad
de niveles de entradas positivas; falta construir la secuencia exacta y
probar sus margenes bancarios en todas las fechas.
Este resultado no establece existencia de esa secuencia, terminalidad,
optimalidad dinamica, bienestar ni correspondencia de equilibrio completo.
La rama B se conserva; no se propone una seleccion de S.

No se ha ejecutado Lean. Las tacticas y la elaboracion de estas declaraciones
deben comprobarse con las dependencias fijadas antes de acreditar el resultado.
La comprobacion futura debe importar este modulo exacto, inspeccionar los
diagnosticos completos y verificar las dependencias y axiomas de sus teoremas.
La revision de significado sigue siendo una comprobacion separada conforme
al protocolo fijado de AppliedModelingLib.
-/

namespace Ventura26LiquidityAllocation

/-- PROPUESTO, SIN COMPILAR. Construye la actividad bilateral de los dos
agregados efectivos y reutiliza la identidad de matching existente. -/
theorem proposed_otcBinaryPair_cancel
    {S : Type*} [Fintype S]
    (P : Primitives S) (tau sMinus sPlus : ℝ)
    (hminus : sMinus < 0) (hplus : 0 < sPlus)
    (hbalance : -sMinus = tau * sPlus) :
    (bankTypeOTCInterbankAt P tau sMinus +
      bankTypeOTCInterbankAt P tau sPlus) / 2 = 0 := by
  have hbilateral :
      BilateralOTCActivity (-sMinus / 2) (sPlus / 2) tau := by
    refine ⟨div_pos (neg_pos.mpr hminus) (by norm_num),
      div_pos hplus (by norm_num), ?_⟩
    rw [hbalance]
    field_simp [ne_of_gt hplus] <;> ring
  have hclear := otcMatchingFractions_clear P.matchingIntensity
    (-sMinus / 2) (sPlus / 2) tau hbilateral
  calc
    (bankTypeOTCInterbankAt P tau sMinus +
        bankTypeOTCInterbankAt P tau sPlus) / 2 =
        otcDeficitMatchFraction P.matchingIntensity tau * (-sMinus / 2) -
          otcSurplusMatchFraction P.matchingIntensity tau * (sPlus / 2) := by
      simp only [bankTypeOTCInterbankAt, if_pos hminus,
        if_neg (not_lt_of_ge hplus.le)]
      ring
    _ = 0 := sub_eq_zero.mpr hclear

/-- PROPUESTO, SIN COMPILAR. Cancelacion de los flujos realmente generados
por fullRetentionCommonBankPlan sobre localSlackPrivateBankCore.
No presupone que la historia sea admisible: basta la igualdad de encaje
en esa historia. La version final la aplica a todas las historias admisibles. -/
theorem proposed_localSlackExpectedInterbank_eq_zero_of_binarySymmetric
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (t : ℕ) (h : History LocalBridgePhase t)
    (htightness : 0 < (d t).controls.tightness)
    (hreserves : 0 < (d t).currentReservesPre)
    (hratio : 0 < localPrefixReserveDepositRatio P (d t))
    (hreserveRate : 0 < (d t).currentReserveRate)
    (hxi : (d t).reserveRequirement <
      (d t).controls.depositRate / (d t).currentReserveRate)
    (hrequirement : P.reserveRequirementPath t h = (d t).reserveRequirement) :
    localSlackExpectedInterbank P d t h = 0 := by
  let tau := (d t).controls.tightness
  let reserves := (d t).currentReservesPre
  let rho := (d t).reserveRequirement
  let xi := (d t).controls.depositRate / (d t).currentReserveRate
  let ratio := localPrefixReserveDepositRatio P (d t)
  let deposits := localPrefixReducedBankDeposits P (d t)
  let amplitude := (xi - rho) * paymentSize * deposits
  let surplusPlus := 2 * amplitude / (1 + tau)

  have hlawParts := hbinary
  rcases hlawParts with ⟨_hne, hsize, _hsupport, _hprobMinus, _hprobPlus,
    hshockMinus, hshockPlus⟩
  have htau : 0 < tau := htightness
  have hden : 0 < 1 + tau := by linarith
  have hdeposits : 0 < deposits := div_pos hreserves hratio
  have hamplitude : 0 < amplitude :=
    mul_pos (mul_pos (sub_pos.mpr hxi) hsize) hdeposits
  have hsurplusPlus : 0 < surplusPlus :=
    div_pos (mul_pos (by norm_num) hamplitude) hden

  -- Reconstruccion de M = r*D desde D = M/r y r > 0.
  have hreserves_eq : reserves = ratio * deposits := by
    change (d t).currentReservesPre =
      localPrefixReserveDepositRatio P (d t) *
        ((d t).currentReservesPre / localPrefixReserveDepositRatio P (d t))
    field_simp [ne_of_gt hratio] <;> ring

  -- La ley binaria descarga el momento absoluto de la formula reducida.
  have hratio_eq : ratio = rho +
      (xi - rho) * paymentSize * (1 - tau) / (1 + tau) := by
    dsimp only [ratio, rho, xi, tau, localPrefixReserveDepositRatio]
    rw [localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
      P paymentMinus paymentPlus paymentSize hbinary]

  -- Realizaciones literales de exceso de reservas, con sus denominadores.
  have hminus_eq :
      bankSettlementSurplus reserves rho xi deposits (-paymentSize) =
        -(tau * surplusPlus) := by
    unfold bankSettlementSurplus
    rw [hreserves_eq, hratio_eq]
    dsimp only [surplusPlus, amplitude]
    field_simp [ne_of_gt hden, ne_of_gt hreserveRate] <;> ring
  have hplus_eq :
      bankSettlementSurplus reserves rho xi deposits paymentSize =
        surplusPlus := by
    unfold bankSettlementSurplus
    rw [hreserves_eq, hratio_eq]
    dsimp only [surplusPlus, amplitude]
    field_simp [ne_of_gt hden, ne_of_gt hreserveRate] <;> ring

  -- Identificacion definicional del flujo del plan, coherente con
  -- fullRetentionCommonBankPlan_candidateFlows. No se usa el placeholder
  -- agregado interbankPosition del constructor privado.
  change finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun omega ↦ bankTypeOTCInterbankAt P tau
      (bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        xi deposits (P.paymentShock omega))) = 0
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric
    P paymentMinus paymentPlus paymentSize hbinary]
  simp only [hrequirement, hshockMinus, hshockPlus]
  change (bankTypeOTCInterbankAt P tau
      (bankSettlementSurplus reserves rho xi deposits (-paymentSize)) +
    bankTypeOTCInterbankAt P tau
      (bankSettlementSurplus reserves rho xi deposits paymentSize)) / 2 = 0
  rw [hminus_eq, hplus_eq]
  exact proposed_otcBinaryPair_cancel P tau (-(tau * surplusPlus)) surplusPlus
    (neg_lt_zero.mpr (mul_pos htau hsurplusPlus)) hsurplusPlus (by ring)

/-- PROPUESTO, SIN COMPILAR. Descarga hinterbank y aplica el teorema existente.
Todas las premisas sobre la secuencia exacta permanecen visibles. -/
theorem proposed_localSlackLiteralAllocation_settlementClears_of_binarySymmetric
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (htightness : ∀ t, 0 < (d t).controls.tightness)
    (hreserves : ∀ t, 0 < (d t).currentReservesPre)
    (hratio : ∀ t, 0 < localPrefixReserveDepositRatio P (d t))
    (hreserveRate : ∀ t, 0 < (d t).currentReserveRate)
    (hxi : ∀ t, (d t).reserveRequirement <
      (d t).controls.depositRate / (d t).currentReserveRate)
    (hrequirement : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h →
        P.reserveRequirementPath t h = (d t).reserveRequirement) :
    SettlementClears P (localSlackLiteralAllocation P I d) := by
  apply localSlackLiteralAllocation_settlementClears P I d htightness
  intro t h hadmissible
  exact proposed_localSlackExpectedInterbank_eq_zero_of_binarySymmetric
    P d paymentMinus paymentPlus paymentSize hbinary t h
    (htightness t) (hreserves t) (hratio t) (hreserveRate t) (hxi t)
    (hrequirement t h hadmissible)

/-!
## Continuacion: historia admisible, encaje y dominio de los datos ensamblados

Todas las declaraciones siguientes son PROPUESTAS SIN COMPILAR.
Se conserva el resultado anterior para todo tau > 0.

El supuesto P.tree = localBridgeTree explicita la especializacion agregada
determinista. No se altera P dentro de una comparacion ni se modifica el modelo
estocastico general. Para el constructor existente P.withLocalBridgeTree,
la igualdad de arboles es definicional.

El lema existente localBridgeTree_historyWeight_pos_iff identifica cualquier
historia admisible con localBridgeHistory t. En las fechas 0 y 1, los
constructores del prefijo evalúan los instrumentos en las mismas historias;
en t = n+2, localRecurrentDateData lo hace literalmente. Asi se deriva la
coincidencia del encaje sin pedirla como premisa del nuevo teorema final.

La positividad de las 33 coordenadas del prefijo y de los seis estados
recurrentes basta para las tasas y reservas que se extraen de esas entradas.
La tightness de controls n sigue siendo una condicion independiente.
En t=n+2 las reservas y su tasa se leen de state (n+1), no de state n.
Los charts logaritmicos preservan positividad solo desde una base positiva.
No prueban por si mismos las ecuaciones ni desigualdades entre coordenadas.

Quedan explicitos dos margenes, con RR > 0 y tau > 0:
  xi > rho  iff  rho*RR < RD,
  rMD > 0   iff  0 < rho*RR*(1+tau) +
                        (RD-rho*RR)*zeta*(1-tau).
La segunda identidad procede de multiplicar rMD por RR*(1+tau) > 0.
Son reformulaciones equivalentes de las cotas pendientes, no certificados de
que una secuencia exacta las satisface.

localSlackExactDateData ensambla entradas arbitrarias. El teorema de abajo no
afirma que estas entradas resuelvan las ecuaciones o que empalmen entre si.
state 0 = Z.stateTwo, controls 0 = tail Z.stateTwo, los residuos exactos,
el padre estacionario y la construccion de la continuacion siguen pendientes
cuando se requiera una secuencia economica exacta.
-/

/-- PROPUESTO, SIN COMPILAR. El encaje de la secuencia ensamblada coincide
con el instrumento primitivo en toda historia de probabilidad positiva. -/
theorem proposed_localSlackExactDateData_reserveRequirement_eq
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen)
    (htree : P.tree = localBridgeTree)
    (t : ℕ) (h : History LocalBridgePhase t)
    (hadmissible : FirmHistoryAdmissible P t h) :
    P.reserveRequirementPath t h =
      (localSlackExactDateData P I Z tail state controls t).reserveRequirement := by
  have hcanonical : h = localBridgeHistory t := by
    apply (localBridgeTree_historyWeight_pos_iff t h).mp
    simpa only [FirmHistoryAdmissible, htree] using hadmissible
  have hzero : bridgeDateZeroHistory P = localBridgeHistory 0 := by
    funext j
    change P.tree.initial = LocalBridgePhase.dateZero
    rw [htree]
    rfl
  have hone : bridgeDateOneHistory P .dateOne = localBridgeHistory 1 := by
    change childHistory (bridgeDateZeroHistory P) .dateOne =
      childHistory (localBridgeHistory 0) .dateOne
    rw [hzero]
  subst h
  cases t with
  | zero =>
      change P.reserveRequirementPath 0 (localBridgeHistory 0) =
        P.reserveRequirementPath 0 (bridgeDateZeroHistory P)
      rw [hzero]
  | succ n =>
      cases n with
      | zero =>
          change P.reserveRequirementPath 1 (localBridgeHistory 1) =
            P.reserveRequirementPath 1 (bridgeDateOneHistory P .dateOne)
          rw [hone]
      | succ n => rfl

/-- PROPUESTO, SIN COMPILAR. El chart de 33 niveles preserva un dominio
positivo ya probado para su base; no prueba que el punto sea una raiz. -/
theorem proposed_localPrefixLogChart_positive
    (Z0 : LocalPrefixCoordinates) (z : Fin 33 → ℝ)
    (hbase : LocalPrefixCoordinatesPositive Z0) :
    LocalPrefixCoordinatesPositive (localPrefixLogChart Z0 z) := by
  have hcoordinate : ∀ j,
      localPrefixCoordinatesVector (localPrefixLogChart Z0 z) j =
        localPrefixCoordinatesVector Z0 j * Real.exp (z j) := by
    intro j
    fin_cases j <;> rfl
  intro j
  rw [hcoordinate]
  exact mul_pos (hbase j) (Real.exp_pos (z j))

/-- PROPUESTO, SIN COMPILAR. El chart de seis estados preserva una base
positiva y no impone restricciones a la funcion independiente controls. -/
theorem proposed_localPrefixStateSixLogChart_positive
    (x0 : LocalPrefixStateSix) (z : Fin 6 → ℝ)
    (hbase : LocalPrefixStateSixPositive x0) :
    LocalPrefixStateSixPositive (localPrefixStateSixLogChart x0 z) := by
  have hcoordinate : ∀ j,
      localPrefixStateSixVector (localPrefixStateSixLogChart x0 z) j =
        localPrefixStateSixVector x0 j * Real.exp (z j) := by
    intro j
    fin_cases j <;> rfl
  intro j
  rw [hcoordinate]
  exact mul_pos (hbase j) (Real.exp_pos (z j))

/-- PROPUESTO, SIN COMPILAR. Extrae las tres cotas bancarias de los dominios
positivos de las entradas. El dominio completo de seis estados es una
condicion suficiente; solo se utilizan sus coordenadas 4 y 5. -/
theorem proposed_localSlackExactDateData_positive_bank_inputs
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen)
    (hprefix : LocalPrefixCoordinatesPositive Z)
    (hstate : ∀ n, LocalPrefixStateSixPositive (state n))
    (hcontrols : ∀ n, 0 < (controls n).tightness) :
    ∀ t,
      0 < (localSlackExactDateData P I Z tail state controls t).controls.tightness ∧
      0 < (localSlackExactDateData P I Z tail state controls t).currentReservesPre ∧
      0 < (localSlackExactDateData P I Z tail state controls t).currentReserveRate := by
  intro t
  cases t with
  | zero => exact ⟨hprefix 16, hprefix 6, hprefix 5⟩
  | succ n =>
      cases n with
      | zero => exact ⟨hprefix 32, hprefix 22, hprefix 21⟩
      | succ n => exact ⟨hcontrols n, hstate (n + 1) 5, hstate (n + 1) 4⟩

/-- PROPUESTO, SIN COMPILAR. Equivalencia del margen de tasas despues de
multiplicar por una tasa de reservas estrictamente positiva. -/
theorem proposed_depositReserveRatio_gt_requirement_iff
    (depositRate reserveRate reserveRequirement : ℝ)
    (hreserveRate : 0 < reserveRate) :
    reserveRequirement < depositRate / reserveRate ↔
      reserveRequirement * reserveRate < depositRate := by
  have hidentity :
      (depositRate / reserveRate - reserveRequirement) * reserveRate =
        depositRate - reserveRequirement * reserveRate := by
    field_simp [ne_of_gt hreserveRate] <;> ring
  constructor
  · intro hratio
    have hpositive := mul_pos (sub_pos.mpr hratio) hreserveRate
    rw [hidentity] at hpositive
    exact sub_pos.mp hpositive
  · intro hmargin
    have hpositive :
        0 < (depositRate / reserveRate - reserveRequirement) * reserveRate := by
      rw [hidentity]
      exact sub_pos.mpr hmargin
    rcases mul_pos_iff.mp hpositive with hboth | hboth
    · exact sub_pos.mp hboth.1
    · exact (not_lt_of_ge hreserveRate.le hboth.2).elim

/-- PROPUESTO, SIN COMPILAR. La razon reducida es positiva exactamente
cuando lo es su numerador despues de multiplicar por RR*(1+tau)>0.
No restringe tau a ser menor que uno. -/
theorem proposed_localPrefixReserveDepositRatio_pos_iff_binaryMargin
    {S : Type*} [Fintype S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hreserveRate : 0 < d.currentReserveRate)
    (htightness : 0 < d.controls.tightness) :
    0 < localPrefixReserveDepositRatio P d ↔
      0 < d.reserveRequirement * d.currentReserveRate * (1 + d.controls.tightness) +
        (d.controls.depositRate - d.reserveRequirement * d.currentReserveRate) *
          paymentSize * (1 - d.controls.tightness) := by
  classical
  have hsum : 0 < 1 + d.controls.tightness := by linarith
  have hden : 0 < d.currentReserveRate * (1 + d.controls.tightness) :=
    mul_pos hreserveRate hsum
  have hidentity :
      localPrefixReserveDepositRatio P d *
          (d.currentReserveRate * (1 + d.controls.tightness)) =
        d.reserveRequirement * d.currentReserveRate * (1 + d.controls.tightness) +
          (d.controls.depositRate - d.reserveRequirement * d.currentReserveRate) *
            paymentSize * (1 - d.controls.tightness) := by
    rw [localPrefixReserveDepositRatio,
      localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
        P paymentMinus paymentPlus paymentSize hbinary]
    field_simp [ne_of_gt hreserveRate, ne_of_gt hsum] <;> ring
  constructor
  · intro hratio
    have hpositive := mul_pos hratio hden
    rw [hidentity] at hpositive
    exact hpositive
  · intro hmargin
    have hpositive : 0 < localPrefixReserveDepositRatio P d *
        (d.currentReserveRate * (1 + d.controls.tightness)) := by
      rw [hidentity]
      exact hmargin
    rcases mul_pos_iff.mp hpositive with hboth | hboth
    · exact hboth.1
    · exact (not_lt_of_ge hden.le hboth.2).elim

/-- PROPUESTO, SIN COMPILAR. Especializa el resultado anterior al constructor
conservado y deriva la premisa de encaje y las tres cotas de niveles.
Los dos margenes siguen visibles como obligaciones sobre la secuencia.
El let solo abrevia la construccion explicita; no contiene una conclusion. -/
theorem proposed_localSlackExactDateData_settlementClears
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (htree : P.tree = localBridgeTree)
    (hprefix : LocalPrefixCoordinatesPositive Z)
    (hstate : ∀ n, LocalPrefixStateSixPositive (state n))
    (hcontrols : ∀ n, 0 < (controls n).tightness) :
    let d := localSlackExactDateData P I Z tail state controls
    (∀ t, (d t).reserveRequirement * (d t).currentReserveRate <
      (d t).controls.depositRate) →
    (∀ t, 0 < (d t).reserveRequirement * (d t).currentReserveRate *
        (1 + (d t).controls.tightness) +
      ((d t).controls.depositRate - (d t).reserveRequirement *
        (d t).currentReserveRate) * paymentSize * (1 - (d t).controls.tightness)) →
    SettlementClears P (localSlackLiteralAllocation P I d) := by
  dsimp only
  intro hspread hmargin
  let d := localSlackExactDateData P I Z tail state controls
  have hpositive := proposed_localSlackExactDateData_positive_bank_inputs
    P I Z tail state controls hprefix hstate hcontrols
  refine proposed_localSlackLiteralAllocation_settlementClears_of_binarySymmetric
    P I d paymentMinus paymentPlus paymentSize hbinary
    (fun t ↦ (hpositive t).1) (fun t ↦ (hpositive t).2.1) ?_
    (fun t ↦ (hpositive t).2.2) ?_ ?_
  · intro t
    exact (proposed_localPrefixReserveDepositRatio_pos_iff_binaryMargin
      P (d t) paymentMinus paymentPlus paymentSize hbinary
      (hpositive t).2.2 (hpositive t).1).mpr (hmargin t)
  · intro t
    exact (proposed_depositReserveRatio_gt_requirement_iff
      (d t).controls.depositRate (d t).currentReserveRate
      (d t).reserveRequirement (hpositive t).2.2).mpr (hspread t)
  · intro t h hadmissible
    exact proposed_localSlackExactDateData_reserveRequirement_eq
      P I Z tail state controls htree t h hadmissible

/-!
## Padre estacionario con captacion bancaria holgada

PROPUESTA SIN COMPILAR. Se extraen como reales exactos las formulas de
paper/paper.tex, sec:v0m_source_25 (lineas 2203--2221), y
code/irf/finite_irf.py, steady_case (lineas 166--229), siempre en el commit
fijado arriba. No se ejecuta ni se identifica el calculo en coma flotante
con estos objetos reales. El testigo anterior de la seccion 21, con limite
de depositos activo, es distinto y no se usa aqui.

Hipotesis del subcaso: betaW=99/100, betaE=24/25, rho=1/10,
zeta=1/5, tau=1/2, corredor=1/50 y matching=log 2. La normalizacion
de cartera del padre es D/E=2, con limites bancarios 4 y 6.

Con v=1/(1+sqrt(3/2)), matching da chiMinus=(1+v)/100 y
chiPlus=v/200. Luego mean=(2+3*v)/400, gap=(2+v)/200 y
A=RD-(9/10)*mean-gap/100. RR es la raiz positiva de
  x^2-A*x-RD*gap/10=0.
Como 0<v<1/2, A>1. El polinomio es positivo en RD porque
  p(RD)=(9/10)*RD*(mean-gap/10)>0.
Asi 1<RR<RD, 1<xi<11/10 y 4/25<rMD<1/6. La ecuacion cuadratica
tambien implica el residual de precios de depositos igual a cero; con
RL=RR+mean resulta RD<RL<25/24.

Los dos puentes finales se refieren a localPrefixDateData y a las filas 8
y 9 realmente conservadas. Sus hipotesis identifican entradas explicitas;
no presuponen sus residuales, el clearing ni un equilibrio.

Esto NO construye un Primitives completo, un padre estacionario completo,
su patrimonio real E>0, un prefijo exacto ni una continuacion. Las cotas
son del punto bancario explicitado. No seleccionan entre las ramas S/B
de garantia empresarial y no establecen cotas para una trayectoria.
-/

namespace ProposedStationaryBank

noncomputable def weight : ℝ :=
  1 / (1 + Real.sqrt (3 / 2 : ℝ))

noncomputable def depositRate : ℝ := 100 / 99

noncomputable def meanSlope : ℝ := (2 + 3 * weight) / 400

noncomputable def slopeGap : ℝ := (2 + weight) / 200

noncomputable def rootCoefficient : ℝ :=
  depositRate - (9 / 10) * meanSlope - slopeGap / 100

noncomputable def reserveRate : ℝ :=
  (rootCoefficient + Real.sqrt
    (rootCoefficient ^ 2 + (2 / 5) * depositRate * slopeGap)) / 2

noncomputable def loanRate : ℝ := reserveRate + meanSlope

noncomputable def reserveDepositRatio : ℝ :=
  1 / 10 + (depositRate / reserveRate - 1 / 10) / 15

/-- Residual de precios bancarios; no es el valor de colateral `s.J`
del script ni la variable heredada de liquidacion empresarial. -/
noncomputable def depositPricingResidual : ℝ :=
  reserveRate + (1 - 1 / 10) * meanSlope -
    (depositRate / reserveRate - 1 / 10) * (1 / 5) * slopeGap / 2 -
    depositRate

/-- PROPUESTO, SIN COMPILAR. Cota exacta de la raiz usada en el matching. -/
theorem weight_bounds : 0 < weight ∧ weight < 1 / 2 := by
  have hsqrt_nonneg := Real.sqrt_nonneg (3 / 2 : ℝ)
  have hsqrt_sq : Real.sqrt (3 / 2 : ℝ) ^ 2 = (3 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_gt : (1 : ℝ) < Real.sqrt (3 / 2 : ℝ) := by
    by_contra h
    have hle : Real.sqrt (3 / 2 : ℝ) ≤ 1 := le_of_not_gt h
    have hproduct :
        0 ≤ (1 - Real.sqrt (3 / 2 : ℝ)) *
          (1 + Real.sqrt (3 / 2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith only [hsqrt_sq, hproduct]
  have hden : 0 < 1 + Real.sqrt (3 / 2 : ℝ) := by linarith
  unfold weight
  constructor
  · exact div_pos (by norm_num) hden
  · apply (div_lt_iff₀ hden).2
    linarith

/-- PROPUESTO, SIN COMPILAR. Especializacion de las funciones OTC reales
del checkpoint; las pendientes no se introducen como parametros libres. -/
theorem matching_specialization (R : ℝ) :
    otcCorridorWeight (Real.log 2) (1 / 2) = weight ∧
    otcDeficitMatchFraction (Real.log 2) (1 / 2) = 1 / 2 ∧
    otcSurplusMatchFraction (Real.log 2) (1 / 2) = 1 / 4 ∧
    otcDeficitSlope R
      (otcNegotiatedRate R (R + 1 / 50) (Real.log 2) (1 / 2))
      (R + 1 / 50) (Real.log 2) (1 / 2) = (1 + weight) / 100 ∧
    otcSurplusSlope R
      (otcNegotiatedRate R (R + 1 / 50) (Real.log 2) (1 / 2))
      (Real.log 2) (1 / 2) = weight / 200 := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hexp : Real.exp (Real.log (2 : ℝ)) = 2 :=
    Real.exp_log (by norm_num)
  have hshare : otcMatchIntensityShare (Real.log 2) = 1 / 2 := by
    unfold otcMatchIntensityShare
    rw [Real.exp_neg, hexp]
    norm_num
  have hweight : otcCorridorWeight (Real.log 2) (1 / 2) = weight := by
    unfold otcCorridorWeight weight
    rw [if_pos hhalf, hexp]
    norm_num
  have hminus : otcDeficitMatchFraction (Real.log 2) (1 / 2) = 1 / 2 := by
    simpa only [otcDeficitMatchFraction, if_pos hhalf] using hshare
  have hplus : otcSurplusMatchFraction (Real.log 2) (1 / 2) = 1 / 4 := by
    rw [otcSurplusMatchFraction, if_pos hhalf, hshare]
    norm_num
  have hrate :
      otcNegotiatedRate R (R + 1 / 50) (Real.log 2) (1 / 2) =
        R + (1 / 50) * weight := by
    rw [otcNegotiatedRate, hweight]
    ring
  refine ⟨hweight, hminus, hplus, ?_, ?_⟩
  · rw [otcDeficitSlope, hminus, hrate]
    ring
  · rw [otcSurplusSlope, hplus, hrate]
    ring

/-- PROPUESTO, SIN COMPILAR. Cotas racionales de las pendientes. -/
theorem slope_bounds :
    0 < meanSlope ∧ meanSlope < 7 / 800 ∧
    0 < slopeGap ∧ slopeGap < 1 / 80 ∧
    0 < meanSlope - slopeGap / 10 := by
  rcases weight_bounds with ⟨hv0, hvhalf⟩
  unfold meanSlope slopeGap
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- PROPUESTO, SIN COMPILAR. La raiz tiene dominio estricto y satisface
la cuadratica exacta, sin evaluar una aproximacion decimal. -/
theorem reserveRate_spec :
    1 < reserveRate ∧ reserveRate < depositRate ∧
    reserveRate ^ 2 - rootCoefficient * reserveRate -
      depositRate * slopeGap / 10 = 0 := by
  rcases slope_bounds with ⟨hmean0, hmeanlt, hgap0, hgaplt, hdiff⟩
  have hdeposit : 0 < depositRate := by norm_num [depositRate]
  have hA : 1 < rootCoefficient := by
    unfold rootCoefficient depositRate
    linarith
  have hAupper : rootCoefficient < depositRate := by
    unfold rootCoefficient
    linarith
  let disc := rootCoefficient ^ 2 + (2 / 5) * depositRate * slopeGap
  have hdisc : 0 ≤ disc := by
    dsimp [disc]
    positivity
  have hsqrt0 := Real.sqrt_nonneg disc
  have hsqrt_sq : Real.sqrt disc ^ 2 = disc := Real.sq_sqrt hdisc
  have hradgap : 0 < (2 / 5 : ℝ) * depositRate * slopeGap := by
    positivity
  have hsqrtA : rootCoefficient < Real.sqrt disc := by
    by_contra h
    have hle : Real.sqrt disc ≤ rootCoefficient := le_of_not_gt h
    have hproduct :
        0 ≤ (rootCoefficient - Real.sqrt disc) *
          (rootCoefficient + Real.sqrt disc) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    dsimp [disc] at hsqrt_sq
    nlinarith
  have hrlo : 1 < reserveRate := by
    change 1 < (rootCoefficient + Real.sqrt disc) / 2
    linarith
  have hpoly :
      reserveRate ^ 2 - rootCoefficient * reserveRate -
        depositRate * slopeGap / 10 = 0 := by
    unfold reserveRate
    dsimp [disc] at hsqrt_sq
    nlinarith only [hsqrt_sq]
  have htest : 0 < depositRate ^ 2 - rootCoefficient * depositRate -
      depositRate * slopeGap / 10 := by
    have hid : depositRate ^ 2 - rootCoefficient * depositRate -
        depositRate * slopeGap / 10 =
        (9 / 10) * depositRate * (meanSlope - slopeGap / 10) := by
      unfold rootCoefficient
      ring
    rw [hid]
    positivity
  have hrhi : reserveRate < depositRate := by
    by_contra h
    have hle : depositRate ≤ reserveRate := le_of_not_gt h
    have hproduct :
        0 ≤ (reserveRate - depositRate) *
          (reserveRate + depositRate - rootCoefficient) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith only [hpoly, htest, hproduct]
  exact ⟨hrlo, hrhi, hpoly⟩

/-- PROPUESTO, SIN COMPILAR. Margenes estrictos y FOC bancarias del punto
exacto. No es un teorema de existencia del equilibrio estacionario. -/
theorem bank_margins_and_pricing :
    1 < depositRate / reserveRate ∧
    depositRate / reserveRate < 11 / 10 ∧
    4 / 25 < reserveDepositRatio ∧ reserveDepositRatio < 1 / 6 ∧
    depositPricingResidual = 0 ∧
    depositRate < loanRate ∧ loanRate < 25 / 24 := by
  rcases reserveRate_spec with ⟨hrlo, hrhi, hpoly⟩
  rcases slope_bounds with ⟨hmean0, hmeanlt, hgap0, _hgaplt, _hdiff⟩
  have hr0 : 0 < reserveRate := by linarith
  have hxi0 : 1 < depositRate / reserveRate := by
    apply (lt_div_iff₀ hr0).2
    simpa using hrhi
  have hxiupper : depositRate / reserveRate < 11 / 10 := by
    apply (div_lt_iff₀ hr0).2
    have hdeposit : depositRate < 11 / 10 := by norm_num [depositRate]
    nlinarith
  have hratio_lo : 4 / 25 < reserveDepositRatio := by
    unfold reserveDepositRatio
    linarith
  have hratio_hi : reserveDepositRatio < 1 / 6 := by
    unfold reserveDepositRatio
    linarith
  have hscaled : depositPricingResidual * reserveRate =
      reserveRate ^ 2 - rootCoefficient * reserveRate -
        depositRate * slopeGap / 10 := by
    unfold depositPricingResidual rootCoefficient
    field_simp [ne_of_gt hr0] <;> ring
  have hpricing : depositPricingResidual = 0 := by
    have hproduct : depositPricingResidual * reserveRate = 0 := by
      rw [hscaled, hpoly]
    exact (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hr0)
  have hloan_gap : loanRate - depositRate =
      (1 / 10) * meanSlope +
        (depositRate / reserveRate - 1 / 10) * slopeGap / 10 := by
    have h := hpricing
    unfold depositPricingResidual at h
    unfold loanRate
    linarith
  have hloanlo : depositRate < loanRate := by
    have hxigap : 0 < depositRate / reserveRate - 1 / 10 := by linarith
    have hpos : 0 < loanRate - depositRate := by
      rw [hloan_gap]
      positivity
    exact sub_pos.mp hpos
  have hloanhi : loanRate < 25 / 24 := by
    unfold loanRate
    norm_num [depositRate] at hrhi
    linarith
  exact ⟨hxi0, hxiupper, hratio_lo, hratio_hi, hpricing, hloanlo, hloanhi⟩

/-- PROPUESTO, SIN COMPILAR. Las carteras normalizadas del padre tienen
margenes estrictos. E>0 sigue siendo una obligacion del cierre real. -/
theorem normalized_portfolio_bounds :
    8 / 25 < 2 * reserveDepositRatio ∧
    2 * reserveDepositRatio < 1 / 3 ∧
    8 / 3 < 3 - 2 * reserveDepositRatio ∧
    3 - 2 * reserveDepositRatio < 67 / 25 := by
  rcases bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, hratio_lo, hratio_hi, _hpricing, _hloanlo, _hloanhi⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- PROPUESTO, SIN COMPILAR. Conecta los margenes exactos con la razon
realmente usada por el constructor. No supone positividad de esa razon. -/
theorem localPrefix_bank_domain
    {S : Type*} [Fintype S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (hreserve : d.currentReserveRate = reserveRate)
    (hdeposit : d.controls.depositRate = depositRate)
    (htightness : d.controls.tightness = 1 / 2)
    (hrequirement : d.reserveRequirement = 1 / 10) :
    0 < d.controls.tightness ∧ 0 < d.currentReserveRate ∧
    d.reserveRequirement < d.controls.depositRate / d.currentReserveRate ∧
    4 / 25 < localPrefixReserveDepositRatio P d ∧
    localPrefixReserveDepositRatio P d < 1 / 6 := by
  classical
  rcases reserveRate_spec with ⟨hrlo, _hrhi, _hpoly⟩
  rcases bank_margins_and_pricing with
    ⟨hxi0, _hxiupper, hratio_lo, hratio_hi, _hpricing, _hloanlo, _hloanhi⟩
  have hratio : localPrefixReserveDepositRatio P d = reserveDepositRatio := by
    rw [localPrefixReserveDepositRatio,
      localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
        P paymentMinus paymentPlus (1 / 5) hbinary,
      hreserve, hdeposit, htightness, hrequirement]
    unfold reserveDepositRatio
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htightness]
    norm_num
  · rw [hreserve]
    linarith
  · rw [hrequirement, hdeposit, hreserve]
    linarith
  · rw [hratio]
    exact hratio_lo
  · rw [hratio]
    exact hratio_hi

/-- PROPUESTO, SIN COMPILAR. Las dos filas bancarias conservadas se anulan
en las entradas exactas del padre. No recibe esos residuales como premisas. -/
theorem localPrefix_bank_pricing_rows
    {S : Type*} [Fintype S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (hmatching : P.matchingIntensity = Real.log 2)
    (hwidth : d.corridorWidth = 1 / 50)
    (hreserve : d.currentReserveRate = reserveRate)
    (hdeposit : d.controls.depositRate = depositRate)
    (hloan : d.controls.loanRate = loanRate)
    (htightness : d.controls.tightness = 1 / 2)
    (hrequirement : d.reserveRequirement = 1 / 10) :
    localReducedRemainingResidual P d 8 = 0 ∧
    localReducedRemainingResidual P d 9 = 0 := by
  classical
  rcases matching_specialization reserveRate with
    ⟨_hweight, _hminus, _hplus, hdeficit, hsurplus⟩
  have hdef : localPrefixBankDeficitSlope P d = (1 + weight) / 100 := by
    simpa only [localPrefixBankDeficitSlope, hreserve, hwidth,
      hmatching, htightness] using hdeficit
  have hsur : localPrefixBankSurplusSlope P d = weight / 200 := by
    simpa only [localPrefixBankSurplusSlope, hreserve, hwidth,
      hmatching, htightness] using hsurplus
  have hmean :
      (localPrefixBankDeficitSlope P d + localPrefixBankSurplusSlope P d) / 2 =
        meanSlope := by
    rw [hdef, hsur]
    unfold meanSlope
    ring
  have hgap : localPrefixBankDeficitSlope P d -
      localPrefixBankSurplusSlope P d = slopeGap := by
    rw [hdef, hsur]
    unfold slopeGap
    ring
  have hmoment := localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    P paymentMinus paymentPlus (1 / 5) hbinary
  rcases bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, _hratio_lo, _hratio_hi, hpricing, _hloanlo, _hloanhi⟩
  constructor
  · change d.controls.loanRate - d.currentReserveRate -
        (localPrefixBankDeficitSlope P d + localPrefixBankSurplusSlope P d) / 2 = 0
    rw [hloan, hreserve, hmean]
    unfold loanRate
    ring
  · change d.currentReserveRate + (1 - d.reserveRequirement) *
        ((localPrefixBankDeficitSlope P d + localPrefixBankSurplusSlope P d) / 2) -
        (d.controls.depositRate / d.currentReserveRate - d.reserveRequirement) *
          localPrefixMeanAbsolutePaymentShock P *
          (localPrefixBankDeficitSlope P d - localPrefixBankSurplusSlope P d) / 2 -
        d.controls.depositRate = 0
    rw [hreserve, hrequirement, hmean, hdeposit, hmoment, hgap]
    exact hpricing

end ProposedStationaryBank

end Ventura26LiquidityAllocation
