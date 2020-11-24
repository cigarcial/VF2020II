# Tarea 2 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

El objetivo en la presente tarea es estudiar los niveles de negación (minimal, intuicionista y clásica) con la que trabaja Coq. 

Se estudia el operador binario de cotenabilidad, definido por 

<img src="https://render.githubusercontent.com/render/math?math=A \circ B := \neg (A \to \neg B)">





Los archivos son los siguientes: 
- Props_LM.v : proposiciones demostradas con lógica minimal. 
- Props_LI.v : proposiciones demostradas con lógica intuicionista. 
- Defs_LC.v : definiciones y notación para el operador cotenable.
- Props_LC.v : proposiciones demostradas con lógica clásica.
- Examples.v : proposiciones probadas con alguno de los tres sistemas. 

Y las dependencias son las siguientes: 

- Props_LC.v <- Defs_LC.v y el módulo de lógica clásica de Coq. 
- Examples.v <- Props_LC.v y el módulo de lógica clásica de Coq.

Es necesario compilar las dependencias antes de usar los archivos mencionados.



