# Tarea 2 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

El objetivo en la presente tarea es estudiar los niveles de negación (minimal, intuicionista y clásica) con los que se puede trabajar en Coq. 

Se verifican algunas propiedades del operador binario de cotenabilidad, <img src="https://render.githubusercontent.com/render/math?math=A \circ B := \neg (A \to \neg B)">, tales como conmuntatividad, asociatividad, distributividad y fusión (<img src="https://render.githubusercontent.com/render/math?math=A \circ B \to C \leftrightarrow (A \to B \to C)">). La verificación de estas propiedades se hace usando la negación al nivel clásico y por ello se incluyen propiedades bien conocidas como la eliminación de la doble negación y las leyes de De Morgan. 

También se verifican algunos argumentos dando uso de cualquiera de los tres sistemas.

Los archivos son los siguientes: 
- Props_LM.v : proposiciones verificadas con lógica minimal. 
- Props_LI.v : proposiciones verificadas con lógica intuicionista. 
- Defs_LC.v : definiciones y notación para el operador cotenable.
- Props_LC.v : proposiciones verificadas con lógica clásica.
- Examples.v : proposiciones verificadas con alguno de los tres sistemas. 

Y las dependencias son las siguientes: 

- Props_LC.v <- Defs_LC.v y el módulo de lógica clásica de Coq. 
- Examples.v <- Props_LC.v y el módulo de lógica clásica de Coq.

Es necesario compilar las dependencias antes de usar los archivos mencionados.



