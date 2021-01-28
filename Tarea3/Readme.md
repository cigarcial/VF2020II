# Tarea 3 - Verificación Formal 
# Unam 2020-II
## Ciro Iván García López - Cta: 520463240

El objetivo en la presente tarea es estudiar la implementación de las operaciones hr y lr de los arreglos flexibles usando árboles de Braun. También se verifican las siguientes propiedades relativas a las operaciones:

1. bsize ( lr t ) = pred ( bsize t ) : 
2. bbal t -> bbal ( lr t )
3. lookup (lr t ) j = lookup t (suc j)
4. lr ( le x t ) = t
5. le ( lookup t Z ) (lr t) = t
6. bsize ( hr t ) = pred ( bsize t) 
7. bbal t -> bbal ( hr t)
8. lookup (hr t) j = lookup t j
9. hr ( he x t ) = t
10. he (lookup t pred(bsize t)) (hr t) = t

Cada archivo consta de dos fragmentos, la primera es el código fuente estudiado durante las sesiones del curos y la segunda el código implementado. La verificación consta de los siguientes archivos:

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
 
