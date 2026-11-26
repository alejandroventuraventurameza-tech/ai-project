# Auditoría del kernel: tres pruebas algebraicas del IE project

**Fecha:** 26 de noviembre de 2026. **Versión académica congelada:** ai-project commit bac3c6255da39cd1169a965df35bb5e9a230e6e8, artículo compacto de ocho resultados. **Compilador:** Lean 4.30.0-rc2. **Librería de referencia:** nikhgarg/AppliedModelingLib, commit 194edcc95df74806a39b961d10dedddc6e730cce.

**Evidencia ejecutada:** [GitHub Actions #45847583114](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847583114), commit e0d07925c43e16e70a3c247509eec2f5d32789a8: **SUCCESS**. El workflow verificó primero la identidad Git de los ocho enunciados originales y después compiló dos archivos Lean autocontenidos.

## Resultados comprobados por el kernel

| Resultado académico | Declaración de especificación | Teorema kernel-verified | Alcance real |
|---|---|---|---|
| **Lema A.1.1**, repago y patrimonio bajo colateral | repaymentCurrentSpec | repaymentCurrent_exact | Demuestra la cobertura real y el patrimonio no negativo, incluyendo depreciación cero. No certifica que todas las historias del equilibrio satisfagan el contrato |
| **Proposición 5.3**, diferencia de precios efectivos entre H y L | effectiveWedgeCurrentSpec | effectiveWedgeCurrent_exact | Demuestra la identidad algebraica de la cuña y su signo, condicionados a precios/tasa positivos y thetaH menor que thetaL; no prueba asignación de equilibrio |
| **Proposición A.1.3**, capital máximo financiable | financingCapacityCurrentSpec | financingCapacityCurrent_exact | Verifica el límite superior para cualquier cartera factible, construye una cartera que alcanza el máximo y demuestra derivada parcial estrictamente negativa; no demuestra que una firma óptima invierta ese máximo |

Los registros de axiomas de las tres declaraciones son exactamente: [propext, Classical.choice, Quot.sound]. No contienen sorryAx, ni se introdujeron axiomas específicos que supongan las conclusiones. La primera campaña detectó errores de tácticas; los logs muestran las correcciones necesarias antes de la compilación final.

**Fuente de los teoremas:** lean/candidates/Ventura26LiquidityAllocation/CurrentCompactWedgeRepayment.lean y lean/candidates/Ventura26LiquidityAllocation/CurrentCompactFinancingCapacity.lean, preservados en PR #6. **Fuente económica:** lean/current_paper_source_inventory_8.json, anclado al commit académico anterior y a los blobs de cada archivo LaTeX.

## Lo que NO acredita la ejecución

Estos son **tres teoremas algebraicos/autocontenidos kernel-verificados**, no tres resultados del paper ya certificados por la auditoría semántica independiente del protocolo oficial. Para declarar correspondencia integral faltan el mapeo fuente→Spec por hipótesis y cuantificador, los enlaces a los estados/historias del modelo económico, una revisión independiente y el chequeo del paquete generado mediante el comando paper_contribution.py check Ventura26LiquidityAllocation --fast.

En el inventario vigente **0/8 equivalencias completas acreditadas** sigue siendo la posición conservadora. Las restantes cinco afirmaciones y sus bloqueos están documentados en RECONCILIACION_ACTUAL_8_20261126.md. Los manuscritos auténticos del autor siguen ausentes (0/8); las guías no son manuscritos.

**Entrega:** se mantiene intacto main. Este documento integra evidencia nueva en [PR #6](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/6) y no altera el PDF ya entregado.
