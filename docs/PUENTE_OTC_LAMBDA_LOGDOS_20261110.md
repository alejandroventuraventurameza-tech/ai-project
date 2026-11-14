# SOURCE OTC / Python: identificacion no trivial de intensidad y dominio

El campo fuente P.matchingIntensity es el parametro estructural lambda. La cuota efectiva de emparejamiento es a_lambda = 1-exp(-lambda). El codigo Python utiliza s.aa=0.5 directamente como cuota, no como lambda. Por eso, **la correspondencia estructural exige lambda=log(2)**, que satisface a_lambda=1/2; introducir erroneamente lambda=.5 en SOURCE no reproduce el experimento Python.

## Branch compatible

Para 0<tau<=1, el SOURCE establece:
- w_lambda(tau) = 1/(1+sqrt(tau+(1-tau)*exp(lambda)))
- fraccion deficit OTC = a_lambda
- fraccion superavit OTC = tau*a_lambda
- tasa OTC = rr + Delta*w_lambda(tau)

Sustituyendo lambda=log 2 se obtiene w=1/(1+sqrt(2-tau)), chi_minus=Delta*(1-aa+aa*w), chi_plus=Delta*tau*aa*w, con aa=1/2. Estas son las formulas literales de Python finite_irf.auxiliary. El valor nominal rr desaparece de las pendientes, como exige la derivacion de diferenciales de tasas. El auditor code/irf/audit_source_otc_log_two_bridge.py examina estas identidades en 12 combinaciones de tau y corredor, y coteja las derivadas en tau y Delta por diferencias centrales contra formulas analiticas.

## Rama no cubierta

El SOURCE cambia su expresion para tau>1: usa w=sqrt(tau^(-1)+(1-tau^(-1))*exp(lambda))/(1+sqrt(...)), fraccion deficitaria a_lambda/tau y fraccion superavitaria a_lambda. Python conserva su formula de tau<=1. La auditoria registra explicitamente un contraejemplo en tau=1.20 y prohíbe inferir equivalencia global del bloque OTC. Para un futuro teorema local de operador se requiere que todo el entorno donde se aplicara la funcion implicita satisfaga tau<1, no solo el valor de referencia tau=.5.

## Estado de evidencia

El nuevo modulo de Lean comprueba cuatro identidades con el SOURCE literal (participacion, peso Nash, ambas pendientes). Solo pueden clasificarse DEMOSTRADAS despues de un CI focalizado del SHA exacto sin sorryAx. El cotejo Python es NUMERICO/CONDICIONAL y solo cubre el bloque OTC. Restan la construccion de Primitives como testigo del caso ilustrativo, las historias, la ley de pagos binaria, el cierre bancario, la igualdad de operadores 33x33 y el equilibrio de horizonte infinito. No fusionar PR #2 a main.
