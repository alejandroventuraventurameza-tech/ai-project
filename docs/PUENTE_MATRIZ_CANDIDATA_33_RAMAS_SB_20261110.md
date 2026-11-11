# Matriz candidata de 33 filas: inversa algebraica, no Jacobiano certificado

Este expediente no afirma igualdad funcional de operadores economicos. Combina nueve factores candidatos log/nivel de las filas SOURCE, dieciseis filas transcritas de factor +1, seis filas empresariales directas y dos Euler empresariales de fecha uno con shear sobre la fila 21 de garantia comun.

En orden SOURCE, defina \`D=diag(lambda_0,...,lambda_32)\`, donde \`lambda_i=1\` fuera del conjunto de nueve escalas. Los nueve factores proceden del archivo \`partial_source_jacobian_row_scale_ledger.json\` calculado **para cada rama**. Para \`i=19,20\`, SOURCE menos Python es \`a_i*g21\` con \`a_i=theta_i*A2*(1/RL1-m_i/Pi2)\`; la derivada de \`g21=log(J2/A2)\` en la raiz con \`J2=A2\` es \`lambda21*d(J2-A2)\`, con \`lambda21=1/A2\`.

Defina \`K\` como la matriz nula salvo \`K[19,21]=-a_H\` y \`K[20,21]=-a_L\`. El operador de filas candidato es \`T=(I+K)*D\`. Como \`K^2=0\`, tenemos **algebraicamente**, sin usar un teorema de equilibrio:

\`\`\`text
T^-1 = D^-1*(I-K),     det(T)=product_i lambda_i.
\`\`\`

El auditor \`code/irf/audit_source_full_transform_candidate.py\` computa ambas inversas numericas y comprueba las identidades matriciales 33x33 y los factores no nulos. **Importante:** para S usa las cantidades de la propia raiz condicional S, nunca los coeficientes de Euler de la estacionariedad B. En el apendice JSON constan los coeficientes separados, hashes y maximos residuos.

La inferencia \`DG=P*T*DF*Dpsi\` es **PENDIENTE**: ni el chequeo de la inversa de T ni la diagonalidad de la carta de niveles demuestran la igualdad de los operadores SOURCE/Python, ni que el Jacobiano fuente sea invertible. Las cartas y los factores aqui propuestos son candidatos algebraicos en un dominio positivo, no certificados de equilibrio dinamico, de optimo global ni de crecimiento endogeno.
