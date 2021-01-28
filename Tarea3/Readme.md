# Tarea 3 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

El objetivo en la presente tarea es estudiar la implementación de las operaciones hr y lr de los arreglos flexibles usando árboles de Braun. También se verifican las siguientes propiedades relativas a las operaciones:

Los archivos son los siguientes: 
- Props_BN.v : proposiciones verificadas con lógica minimal. 
- Props_BT.v : proposiciones verificadas con lógica intuicionista. 
- Defs_BN.v : definiciones y notación para el operador cotenable.
- Defs_BT.v : proposiciones verificadas con alguno de los tres sistemas. 

Y las dependencias son las siguientes: 

- Props_BN.v <- Defs_BN.v . 
- Defs_BT.v <- Defs_BN.v y Props_BN.v .
- Props_BT.v <- Defs_BN.v, Props_BN.v y Defs_BT.v .

Es necesario compilar las dependencias antes de usar los archivos mencionados.

### Referencias:

1. Rob R. Hoogerwoord.  A logarithmic implementation of flexible arrays.  In R. S. Bird, C. C.Morgan, and J. C. P. Woodcock, editors,Mathematics of Program Construction, pages 191–207,Berlin, Heidelberg, 1993. Springer Berlin Heidelberg
 
