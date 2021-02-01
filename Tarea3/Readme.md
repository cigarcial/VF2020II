# Tarea 3 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

El objetivo de la presente tarea es estudiar la implementación de las operaciones hr y lr de los arreglos flexibles usando árboles de Braun. Adicionalmente se verifican las siguientes propiedades relativas a las operaciones:

1. bsize ( lr t ) = pred ( bsize t ) 
2. bbal t -> bbal ( lr t )
3. lookup (lr t ) j = lookup t (suc j)
4. lr ( le x t ) = t
5. le ( lookup t Z ) (lr t) = t
6. bsize ( hr t ) = pred ( bsize t) 
7. bbal t -> bbal ( hr t)
8. lookup (hr t) j = lookup t j
9. hr ( he x t ) = t
10. he (lookup t pred(bsize t)) (hr t) = t

Las pruebas de estas propiedades se hacen por inducción sobre la estructura del árbol o sobre el hecho de *ser árbol de Braun*.

Cada archivo de Coq se divide en dos fragmentos: en la primera está el código estudiado durante las sesiones del curso y en la segunda el código implementado. La verificación se compone de los siguientes archivos:

- Props_BN.v : proposiciones verificadas con lógica minimal. 
- Props_BT.v : proposiciones verificadas con lógica intuicionista. 
- Defs_BN.v : definiciones y notación para el operador cotenable.
- Defs_BT.v : proposiciones verificadas con alguno de los tres sistemas. 

Y las dependencias son las siguientes entre los archivos son: 

- Props_BN.v <- Defs_BN.v . 
- Defs_BT.v <- Defs_BN.v y Props_BN.v .
- Props_BT.v <- Defs_BN.v, Props_BN.v y Defs_BT.v .

Es necesario compilar las dependencias antes de usar el archivo en cuestión.

### Referencias:

1. Rob R. Hoogerwoord.  A logarithmic implementation of flexible arrays.  In R. S. Bird, C. C.Morgan, and J. C. P. Woodcock, editors,Mathematics of Program Construction, pages 191–207,Berlin, Heidelberg, 1993. Springer Berlin Heidelberg
 
