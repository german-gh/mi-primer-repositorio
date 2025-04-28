import System.Win32 (xBUTTON1)
{-
--Ejercicio 1
{-
problema f (n : Z) : Z {
requiere: {n = 1 ∨ n = 4 ∨ n = 16}
asegura: {(n = 1 → res = 8) ∧ (n = 4 → res = 131) ∧ (n = 16 → res = 16)}
}
-}
f :: Integer -> Integer
f 1 = 8
f 4 = 131
f 16 = 16

{-
problema g (n : Z) : Z {
    requiere: {n = 8 o n = 16 o n = 131}
    asegura: {(n = 8 -> res = 16) y (n = 16-> res = 4) y (n = 131 -> res = 1) 
}
-}
g :: Integer -> Integer
g 8 = 16
g 16 = 4
g 131 = 1

{-
problema h (n : Z) : Z {
    requiere: {n = 8 o n = 16 o n = 131}
    asegura: {(n = 8 -> res = 16) y (n = 16 -> res = 131) y (n = 131 -> res = 8) 
}
problema k (n : Z) : Z {
    requiere: {n = 1 o n = 4 o n = 16}
    asegura: {(n = 1 -> res = 16) y (n = 4 -> res = 1) y (n = 16 -> res = 4) 
}
-}
h :: Integer -> Integer
h n = f(g n)

k :: Integer -> Integer
k n = g(f n)
-}

{------------------------------}
--Ejercicio 2
{-
problema absoluto (n : Z) : Z {
    requiere: {True}
    asegura: {res = |n| >= 0}
}
-}
absoluto :: Integer -> Integer
absoluto n | n == 0 = 0
           | n > 0 = n
           | n < 0 = -n

{-
problema maximoAbsoluto (a:Z, b:Z) : Z{
    requiere: {True}
    asegura: {(absoluto a > absoluto b -> res = absoluto a) y
              (absoluto b > absoluto a -> res = absoluto b) y
              (absoluto a = absoluto b -> res = absoluto a)}
}
-}
maximoAbsoluto :: Integer -> Integer -> Integer
maximoAbsoluto a b | absoluto a == absoluto b = absoluto a
                   | absoluto a > absoluto b = absoluto a
                   | absoluto b > absoluto a = absoluto b

{-
problema maximo3 (a: Z, b:Z ,c:Z): Z {
    requiere: {True}
    asegura: {devuelve el maximo entre tres numeros enteros}
-}
maximo3 :: Integer -> Integer -> Integer -> Integer
maximo3 a b c | a >= b && a >= c = a
              | b >= c = b
              | otherwise = c

{-
problema algunoEsCero (a:Q, b:Q) : Bool {
    requiere: {a y b racionales}
    asegura: {(si a == 0 o b == 0) -> res = True}
    asegura: {(si a \= 0 y b \= 0) -> res = False}
}
-}
--Sin Pattern Matching
algunoEsCero :: Float -> Float -> Bool
algunoEsCero a b | a == 0 || b == 0 = True
                 | otherwise = False
--Con Pattern Matching
algunoEsCeroPM :: Float -> Float -> Bool
algunoEsCeroPM 0 b = True
algunoEsCeroPM a 0 = True
algunoEsCeroPM _ _ = False

{-
problema ambosSonCero (a:Q, b:Q) : Bool {
    requiere: {a y b racionales}
    asegura: {(si a == 0 y b == 0) -> res = True}
    asegura: {(si a \= 0 o b \= 0) -> res = False}
}
-}
--Sin Pattern Matching
ambosSonCero :: Float -> Float -> Bool
ambosSonCero a b | a == 0 && b == 0 = True
                 | otherwise = False
--Con Pattern Matching
ambosSonCeroPM :: Float -> Float -> Bool
ambosSonCeroPM 0 0 = True
ambosSonCeroPM _ _ = False

{-
problema enMismoIntervalo (a:R, b:R) : Bool {
    requiere {relacion de equivalencia en R cuyas 
                clases de equivalencia, [x], son: (−∞, 3], (3, 7] y (7, ∞)}
    asegura {[a] == [b] -> res = True}
    asegura {[a] \= [b] -> res = False}
}
-}
enMismoIntervalo :: Float -> Float -> Bool
enMismoIntervalo a b | a <= 3 && b <= 3 = True
                     | a > 3 && a <= 7 && b > 3 && b <= 7 = True
                     | a > 7 && b > 7 = True
                     | otherwise = False

{-
problema sumaDistintos (a:Z, b:Z, c:Z) : Z {
    requiere {True}
    asegura {dados 3 numeros enteros calcule la suma 
            sin sumar repetidos (si los hubiera)}
}
-}
sumaDistintos :: Integer -> Integer -> Integer -> Integer
sumaDistintos a b c | a == b && a == c && b == c = 0
                    | a == b && a /= c = c
                    | a == c && a /= b = b
                    | b == c && b /= a = a
                    | otherwise = a+b+c

{-
problema esMultiploDe (a:N, b:N) : Bool {
    requiere {numeros naturales}
    asegura {dados 2 numeros naturales, decide si el
            primero es multiplo del segundo: a = bn)}
}
-}
esMultiploDe :: Integer -> Integer -> Bool
esMultiploDe a b | a `mod` b == 0 = True
                 | otherwise = False

{-
problema digitoUnidades (a:Z) : Z {
    requiere {numeros enteros}
    asegura {dado un numero entero, extrae
            su dıgito de las unidades)}
}
-}
digitoUnidades :: Integer -> Integer
digitoUnidades a = (absoluto a) `mod` 10

{-
problema digitoDecenas (a:Z) : Z {
    requiere {a > 9}
    asegura {dado un numero entero mayor a 9,
            extrae su d´ıgito de las decenas.)}
}
-}
digitoDecenas :: Integer -> Integer
digitoDecenas a = digitoUnidades (eliminarUltimoDigito a)
    where eliminarUltimoDigito a = a `div` 10

{------------------------------}
--Ejercicio 3. 
{-
problema estanRelacionados (a : Z, b : Z) : Bool {
    requiere: {a ̸= 0 ∧ b ̸= 0}
    asegura: {(res = true) ↔ (a ∗ a + a ∗ b ∗ k = 0 
                para algun k ∈ Z con k ̸= 0)
    asegura { k = -a/b}}
}
-}
estanRelacionados :: Integer -> Integer -> Bool
estanRelacionados a b | (absoluto a) `mod` (absoluto b) == 0 = True
                      | otherwise = False

{------------------------------}
--Ejercicio 4.
{-
problema productoInterno ((a1,a2): RxR, (b1,b2): RxR) : RxR) {
    requiere: {True}
    asegura: {(calcula el producto interno entre 2 
                tuplas de RxR)
}
-}
productoInterno :: (Float, Float) -> (Float, Float) -> Float
productoInterno (a1,a2) (b1,b2) = a1*b1 + a2*b2

productoInterno2 :: (Float, Float) -> (Float, Float) -> Float
productoInterno2 x y = fst x * fst y + snd x * snd y

{-
problema esParMenor ((a1,a2): RxR, (b1,b2): RxR) : Bool) {
    requiere: {True}
    asegura: {(dadas dos tuplas de RxR, decide si cada coordenada
            de la primera tupla es menor a la coordenada 
            correspondiente de la segunda tupla)
}
-}
esParMenor:: (Float,Float) -> (Float,Float) -> Bool
esParMenor (a1,a2) (b1,b2) = a1 < b1 && a2 < b2 

{-
problema distancia ((a1,a2): RxR, (b1,b2): RxR) : R) {
    requiere: {True}
    asegura: {calcula la distancia euclidea entre dos puntos de R2}
}
-}
distancia :: (Float,Float) -> (Float,Float) -> Float
distancia (a1,a2) (b1,b2) = sqrt ((a1 - b1)^2 + (a2 - b2)^2)

{-
problema sumaTerna ((x,y,z): ZxZxZ) : Z) {
    requiere: {True}
    asegura: {dada una terna de enteros, calcula la
            suma de sus tres elementos}
}
-}
sumaTerna :: (Integer, Integer, Integer) -> Integer
sumaTerna (x,y,z) = x+y+z

{-
problema sumarSoloMultiplos ((x,y,z): ZxZxZ, n: N) : Z) {
    requiere: {True}
    asegura: {dada una terna de numeros enteros y un natural,
        calcula la suma de los elementos de la terna que
        son multiplos del numero natural}
}
-}
sumarSoloMultiplos :: (Integer, Integer, Integer) -> Integer -> Integer
sumarSoloMultiplos (x,y,z) n 
    | esMultiploDe x n && esMultiploDe y n && esMultiploDe z n = x+y+z
    | esMultiploDe x n && esMultiploDe y n = x+y
    | esMultiploDe x n && esMultiploDe z n = x+z
    | esMultiploDe y n && esMultiploDe z n = y+z
    | esMultiploDe x n = x
    | esMultiploDe y n = y
    | esMultiploDe z n = z
    | otherwise = 0

{-
problema posPrimerPar ((x,y,z): ZxZxZ) : Z) {
    requiere: {True}
    asegura: {dada una terna de enteros, devuelve la
        posicion del primer numero par si es que hay alguno,
        o devuelve 4 si son todos impares}
}

-}
posPrimerPar :: (Integer, Integer, Integer) -> Integer
posPrimerPar (x,y,z) | esPar x = 1
                     | esPar y = 2
                     | esPar z = 3
                     | otherwise = 4
    where esPar n = mod n 2 == 0    

{-
problema crearPar ((x,y,z): ZxZxZ) : Z) {
    requiere: {True}
    asegura: {a partir de dos componentes,
        crea un par con esos valores.
        Debe funcionar para elementos de cualquier tipo}
}
-}
crearPar :: a -> b -> (a, b)
crearPar a b = (a,b)

{-
problema invertir ((x,y,z): ZxZxZ) : Z) {
    requiere: {True}
    asegura: {invierte los elementos del par pasado
        como parametro. Debe funcionar para elementos
        de cualquier tipo}
}
-}
invertir :: (a, b) -> (b, a)
invertir (a, b) = (b, a)


--renombre de tipos:
type Punto2D = (Float, Float)

productoInternoR :: Punto2D -> Punto2D -> Float
productoInternoR (a1,a2) (b1,b2) = a1*b1 + a2*b2

esParMenorR:: Punto2D -> Punto2D -> Bool
esParMenorR (a1,a2) (b1,b2) = a1 < b1 && a2 < b2 

distanciaR :: Punto2D -> Punto2D -> Float
distanciaR (a1,a2) (b1,b2) = sqrt ((a1 - b1)^2 + (a2 - b2)^2)

{------------------------------}
--Ejercicio 5.
{-
problema todosMenores (t : Z × Z × Z) : Bool {
requiere: {True}
asegura: {(res = true) ↔ ((f(t0) > g(t0)) ∧
                            (f(t1) > g(t1)) ∧
                            (f(t2) > g(t2)))}
}
-}
todosMenores :: (Integer, Integer, Integer) -> Bool
todosMenores (t0,t1,t2) = (f(t0) > g(t0)) && (f(t1) > g(t1)) && (f(t2) > g(t2))

{-
problema f (n : Z) : Z {
requiere: {True}
asegura: {(n ≤ 7 → res = n^2) y (n > 7 → res = 2n − 1)}
}
-}
f :: Integer -> Integer
f n | n <= 7 = n^2
    | n > 7 = 2*n -1

{-
problema g (n : Z) : Z {
requiere: {True}
asegura: {Si n es un numero par entonces res = n/2,
            en caso contrario, res = 3n + 1}
}
-}
g :: Integer -> Integer
g n | n `mod` 2 == 0 = n `div` 2
    | otherwise = 3*n +1

--Ejercicio 6
type Anio = Integer
type EsBisiesto = Bool
{-
problema bisiesto (año : Z) : Bool {
requiere: {True}
asegura: {(res = false) ↔ (año no es multiplo de 4,
            o bien, año es multiplo de 100 pero no de 400)}
}
-}
--Bisiesto = anio mod 4 == True y (anio mod 400 == True o not (anio mod 100 == True))
bisiesto :: Anio -> EsBisiesto
bisiesto anio = (anio `mod` 4 == 0) && 
                (anio `mod` 400 == 0 || not (anio `mod` 100 == 0)) 

--Ejercicio 7.
{-
problema distanciaManhattan (p : R × R × R, q : R × R × R) : R {
requiere: {True}
asegura: {res = Sumatoria, 0<= i <=2, |pi − qi|}
-}

absolutoR :: Float -> Float
absolutoR x | x == 0 = 0
            | x > 0 = x
            | x < 0 = -x

distanciaManhattan :: (Float, Float, Float) -> (Float, Float, Float) -> Float
distanciaManhattan (x0,x1,x2) (y0,y1,y2) = absolutoR (x0-y0) +  absolutoR (x1-y1) +  absolutoR (x2-y2)

--Reimplementar la funci´on teniendo en cuenta el siguiente tipo
type Punto3D = (Float, Float, Float)

distanciaManhattan2 :: Punto3D -> Punto3D -> Float
distanciaManhattan2 (x0,x1,x2) (y0,y1,y2) = absolutoR (x0-y0) +  absolutoR (x1-y1) +  absolutoR (x2-y2)

--Ejercicio 8
{-
problema comparar (a : Z, b : Z) : Z {
requiere: {True}
asegura: {(res = 1) ↔ (sumaUltimosDosDigitos(a) < sumaUltimosDosDigitos(b))}
asegura: {(res = −1) ↔ (sumaUltimosDosDigitos(a) > sumaUltimosDosDigitos(b))}
asegura: {(res = 0) ↔ (sumaUltimosDosDigitos(a) = sumaUltimosDosDigitos(b))}
}
-}
comparar :: Integer -> Integer -> Integer
comparar a b | sumaUltimosDosDigitos(a) < sumaUltimosDosDigitos(b) = 1
             | sumaUltimosDosDigitos(a) > sumaUltimosDosDigitos(b) = -1
             | sumaUltimosDosDigitos(a) == sumaUltimosDosDigitos(b) = 0

{-
problema sumaUltimosDosDigitos (x : Z) : Z {
requiere: {True}
asegura: {res = ( |x| mod 10 ) + ( ||x|/10| mod 10)}
}
-}
sumaUltimosDosDigitos :: Integer -> Integer
sumaUltimosDosDigitos x = ((absoluto x) `mod` 10) + ((absoluto x) `div` 10) `mod` 10

--Ejercicio 9. A partir de las siguientes implementaciones en Haskell, describir en lenguaje natural que hacen y especificarlas.

{-
problema f1 (n : R) : R {
    requiere: {True}
    asegura: {(n = 0 -> res = 1) y (n /= 0 -> res = 0)}
}
-}
f1 :: Float -> Float
f1 n | n == 0 = 1
     | otherwise = 0

{-
problema f2 (n : R) : R {
    requiere: { n pertenesca a {1,-1} }
    asegura: { (n = 1 -> res = 15) y (n = -1 -> res = -15) }
}
-}
f2 :: Float -> Float
f2 n | n == 1 = 15
     | n == -1 = -15

{-
problema f3 (n : R) : R {
    requiere: {True }
    asegura: { (n <= 9 -> res = 7) y (n > 9 -> res = 5)  }
}
-}
f3 :: Float -> Float
f3 n | n <= 9 = 7
     | n >= 3 = 5

{-
problema f4 (x : R, y : R) : R {
    requiere: {True}
    asegura: {res es el promedio de x e y}
}
-}
f4 :: Float -> Float -> Float
f4 x y = (x+y)/2

{-
problema f5 (d = R x R) : R {
    requiere: {True}
    asegura: {res es el promedio de las coordenadas x e y}
}
-}
f5 :: (Float , Float ) -> Float
f5 (x, y) = (x+y)/2

{-
problema f6 (a: R, b: Z) : Bool {
    requiere: {True}
    asegura: {res = True si la parte entera de a es igual a la de b. Caso contrario res = False}
}
-}
f6 :: Float -> Int -> Bool
f6 a b = truncate a == b