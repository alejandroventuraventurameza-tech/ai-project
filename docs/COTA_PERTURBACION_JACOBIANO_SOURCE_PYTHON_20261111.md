# IE Project 18 — condición cuantitativa para transportar invertibilidad (11-XI-2026)

**Estatus:** proposición matemática condicional, no teorema de equilibrio SOURCE; documento ligado a la auditoría del commit `f55b8402d15ac88908a8209400d8ea78cd873842`.

## A. Orientación y regla de la cadena

Sean `F:U⊂R^33→R^33` (SOURCE), `G:V⊂R^33→R^33` (Python), `psi:V→U` y `T:V→R^{33×33}`. La matriz `P` reordena las filas de SOURCE al orden Python. Si existe una identidad funcional **exacta en un entorno abierto** `G(z)=P T(z) F(psi(z))`, se tiene

`DG(z)[h]=P DT(z)[h]F(psi(z)) + P T(z)DF(psi(z))Dpsi(z)[h]`.

En una raíz `F(psi(z*))=0`:

`DG(z*) = P T(z*) DF(psi(z*)) Dpsi(z*)`.

Si `T(z*)`, `Dpsi(z*)` son invertibles, entonces `DG(z*)` es invertible si y solo si `DF(psi(z*))` es invertible. Las matrices candidatas del repositorio no justifican por sí solas `G=PTFpsi` ni `DF^{-1}`.

La fórmula para recuperar la inversa SOURCE **si DG es invertible** es

`DF(psi(z*))^{-1} = Dpsi(z*) DG(z*)^{-1} P T(z*)`.

Por submultiplicatividad, con la norma infinito:

`||DF^{-1}||∞ ≤ ||Dpsi||∞ ||DG^{-1}||∞ ||P||∞ ||T||∞`.

Para una matriz de permutación, `||P||∞=1`. Por tanto, aun cuando `T^{-1}` existe, una cota de `||T^{-1}||` **no sustituye** una cota de `||DG^{-1}||`.

## B. Si la igualdad funcional todavía tiene un resto

Supóngase `G(z)=P T(z)F(psi(z))+R(z)`, con `R` diferenciable. Exigir `F(psi(z*))=0` y `R(z*)=0` permite construir el mismo cero. Su Jacobiano satisface

`DG(z*)=M+E`, donde `M=P T(z*)DF(psi(z*))Dpsi(z*)`, `E=DR(z*)`.

Si se certifica que `M` es invertible y que

`q=||M^{-1}E||∞<1`,

la serie de Neumann demuestra que `DG(z*)` es invertible, con

`||DG(z*)^{-1}||∞ ≤ ||M^{-1}||∞/(1-q)`.

**Advertencia:** también se puede transferir en la dirección inversa si se parte de un `DG` invertible y se acota `||DG^{-1}E||∞<1`; los dos tests no son intercambiables sin las cotas necesarias. Un resto pequeño solo en valor `R(z*)` no controla `DR(z*)`.

## C. Obligaciones para el repositorio

1. Construir `psi` como carta abierta, verificar dominio, orientación y `Dpsi` invertible.
2. Cotejar **las 33 funciones económicas** SOURCE–Python con los mismos estados heredados, parámetros y cronología de las cuatro herramientas monetarias.
3. Obtener un acotamiento de `DR` válido en un entorno (si no se obtiene identidad exacta); no basta evaluar dos trayectorias.
4. Certificar `DG^{-1}` o `DF^{-1}` mediante un método riguroso independiente: aritmética intervalar, validación a posteriori o prueba en Lean. No sustituirlo por inversión de `T` ni por un solve de punto flotante.
5. Distinguir la rama S/B y la condición de complementariedad, además de los estados heredados; mantener separada la frontera `make_boundary` de dos raíces distintas.
6. Tras la regularidad local, demostrar condiciones KKT completas, suficiencia, terminalidad y existencia de equilibrio infinito antes de afirmar efectos sobre crecimiento permanente.

## D. Evidencia CI existente

La revisión `f55b840` registra ocho workflows en verde:

- [build #43056988739](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988739)
- [editorial-qa #43056988757](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988757)
- [Lean política/pagos #43056988878](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988878)
- [Lean garantía #43056988688](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988688)
- [Lean proposiciones #43056988834](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988834)
- [Lean frontera #43056988802](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988802)
- [puente stencil #43056988745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988745)
- [same-predecessor tail #43056988911](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43056988911)

Estos certificados corresponden solo a sus jobs y al SHA. **Ni un CI verde ni la presente proposición algebraica prueban la igualdad económica de los 33 residuos o la invertibilidad del Jacobiano SOURCE.**

Conservar PR #2 como borrador y `main` sin fusionar.
