# Puente estacionario SOURCE para cuatro intervenciones iniciales y pagos OTC

**Objeto:** conectar la instancia de `Primitives LocalBridgePhase` construida en `StationaryPrimitivesCandidate.lean` y ya compilada, con el registro transformado por `initialIntervenedPrimitives`. No se reconstruye un testigo preexistente.

## Seis resultados del módulo

`StationaryInterventionSourceBridgeCandidate.lean` importa la instancia estacionaria y las igualdades OTC del SOURCE. Para todo valor de la deuda pública `G` y toda intervención inicial `v`, propone demostrar: (1) que permanece vigente la ley binaria con pagos de `-1/5` y `+1/5`, equiprobables; (2) el momento absoluto `E|ω|=1/5` que identifica `s.zeta=0.2` en Python; (3) que el factor de renovación bancaria sigue siendo `1/Rstar`; (4) la igualdad exacta de la razón reservas-depósitos `h=rho+(RD/RR-rho)*zeta*(1-tau)/(1+tau)`; (5) la coincidencia de la pendiente OTC de déficit con la fórmula Python para `tau<=1`; y (6) la misma coincidencia para la pendiente de superávit.

Los dos últimos resultados requieren `tau<=1`. El experimento económico exige también `tau>0`. No cabe ampliar la equivalencia a `tau>1`, pues el SOURCE usa otra rama de la función OTC.

El workflow `lean-stationary-policy-payment-bridge.yml` restaura el SOURCE y las dependencias fijadas, compila el nuevo módulo e inspecciona los resultados de `#print axioms`. Los resultados nuevos son **PENDIENTES** hasta una ejecución verde del SHA exacto.

## Alcance

Estas identidades conectan una instancia real de `Primitives` con funciones fuente de pagos, encajes y liquidez. No establecen que los controles de `decode_prefix` de Python coincidan con el mismo `LocalPrefixDateData`, ni equivalencia de las 33 funciones, invertibilidad del Jacobiano SOURCE, existencia de equilibrio, optimalidad bancaria ni efectos de crecimiento permanente.

Conservar PR #2 como borrador; no fusionar a `main`.
