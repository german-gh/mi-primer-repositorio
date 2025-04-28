absolutoI :: Integer -> Integer
absolutoI x | x == 0 = 0
            | x > 0 = x
            | x < 0 = -x

absolutoF :: Float -> Float
absolutoF x | x == 0 = 0
            | x > 0 = x
            | x < 0 = -x


absoluto :: (Num a, Ord a) => a -> a
absoluto x  | x == 0 = 0
            | x > 0 = x
            | x < 0 = -x

negar :: Num a => a -> a
negar x = -x

digitoUnidades :: Integer -> Integer
digitoUnidades a = (absolutoI a) `mod` 10

eliminarUltimoDigito :: Integer -> Integer
eliminarUltimoDigito a = a `div` 10

digitoDecenas :: Integer -> Integer
digitoDecenas a = digitoUnidades (eliminarUltimoDigito a)

eliminarPrimerDigito :: Integer -> Integer
eliminarPrimerDigito n = n - (primerDigito n * 10^(cantDigitos n - 1))

eliminarUltimosDigitos :: Integer -> Integer-> Integer
eliminarUltimosDigitos n i
    | i > cantDigitos n = 0
    | i == cantDigitos n = 0
    | otherwise = div n (10^(i))

primerDigito :: Integer -> Integer
primerDigito n = n `div` 10^(cantDigitos n - 1)

factorialG :: Integer -> Integer
factorialG n
    | n == 0 = 1
    | otherwise = n * factorialG (n-1)

factorialPM :: Integer -> Integer
factorialPM 0 = 1
factorialPM n = n * factorialPM (n-1)

factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n-1)

--Ejercicio 1
{-
problema fibonacci (n: Z) : Z {
requiere: { n ≥ 0 }
asegura: { resultado = fib(n) }
}
-}
fibonacci:: Integer -> Integer 
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci (n-2) + fibonacci (n-1)

--Ejercicio 2
{-
problema parteEntera (x: R) : Z {
requiere: { x ≥ 0 }
asegura: { resultado ≤ x < resultado + 1 }
}
-}
parteEntera :: Float -> Integer
parteEntera x = buscadorEntero 0
    where buscadorEntero n
            | fromIntegral n <= x = buscadorEntero (n+1)
            | otherwise = n-1

parteEntera2 :: Float -> Integer
parteEntera2 x 
    | x >= 0 && x < 1 = 0
    | x >= 1 = 1 + parteEntera2 (x - 1)

{-
parteEntera :: Float -> Integer
parteEntera x 
    | x >= 0 = buscadorEntero 0
    | x < 0 =  negar (buscadorEntero 0)
    where buscadorEntero n
                | fromIntegral n <= absolutoF x = buscadorEntero (n+1)
                | otherwise = n-1
-}

--Ejercicio 3
{-
problema esDivisible (a, b: Z) : Bool {
requiere: { a >= 1 y b >= 1 }
asegura: { res = True sii b|a }
}
-}
esDivisible :: Integer -> Integer -> Bool
esDivisible a b
    | a == b = True
    | a < b = False
    | a > b = esDivisible (a - b) b

--Ejercicio 4
{-
problema sumaImpares (n: Z) : Z {
requiere: { n >= 1 }
asegura: { res = la suma de los primeros n numeros impares }
}
-}
sumaImpares :: Integer -> Integer
sumaImpares n
    | n == 1 = 1
    | otherwise = (2*n-1) + sumaImpares (n-1)

--Ejercicio 5
{-
problema medioFact (n: Z) : Z {
requiere: { n ≥ 0 }
asegura: { resultado = doble factorial}
}
-}
medioFact :: Integer -> Integer
medioFact 0 = 1
medioFact 1 = 1
medioFact n = n * medioFact (n-2)

-- Ejercicio 6
{-
problema todosDigitosIguales (n: Z) : Bool {
requiere: { n > 0 y No empiece por 0}
asegura: { resultado = true ↔ todos los digitos de n son iguales }
}
-}
todosDigitosIguales :: Integer -> Bool
todosDigitosIguales n
    | n <= 9 = True
    | digitoDecenas n /= digitoUnidades n = False
    | digitoDecenas n == digitoUnidades n = todosDigitosIguales (eliminarUltimoDigito n)

--Ejercicio 7
{-
problema iesimoDigito (n: Z, i: Z) : Z {
requiere: { n ≥ 0 ∧ 1 ≤ i ≤ cantDigitos(n) }
asegura: { resultado = (n div 10^(cantDigitos(n)−i)) mod 10 }
}
-}
iesimoDigito :: Integer -> Integer -> Integer
iesimoDigito n i
    | cantDigitos n == 1 = n
    | otherwise = digitoUnidades (eliminarUltimosDigitos n ((cantDigitos n)-i))

iesimoDigito2 :: Integer -> Integer -> Integer
iesimoDigito2 n i
    | i == cantDigitos n = digitoUnidades n
    | cantDigitos n < i = -1
    | otherwise = iesimoDigito2 (eliminarUltimoDigito n) i

{-
problema cantDigitos (n: Z) : N {
requiere: { n ≥ 0 }
asegura: { n = 0 → resultado = 1}
asegura: { n ̸= 0 → (n div 10resultado−1 > 0 ∧ n div 10resultado = 0) }
}
-}
cantDigitos :: Integer -> Integer
cantDigitos n
    | n <= 9 = 1
    | otherwise = 1 + cantDigitos (eliminarUltimoDigito n)

--Ejercicio 8
{-
problema sumaDigitos (n: Z) : Z {
requiere: { n ≥ 0 }
asegura: { res = suma de todos los digitos de n}
}
-}
sumaDigitos :: Integer ->Integer
sumaDigitos n
    | cantDigitos n == 1 = n
    | otherwise = (digitoUnidades n) + (sumaDigitos (eliminarUltimoDigito n))

--Ejercicio 9
{-
problema esCapicua (n: Z) : Bool {
requiere: { n ≥ 0 }
asegura: { res = True sii (n es capicua o tiene un solo digito) }
}
-}

esCapicua :: Integer -> Bool
esCapicua n = comparadorDeExtremos n (cantDigitos n) 1

comparadorDeExtremos :: Integer -> Integer -> Integer -> Bool
comparadorDeExtremos n incio final
    | incio < final = True
    | iesimoDigito n incio /= iesimoDigito n final = False
    | otherwise = comparadorDeExtremos n (incio-1) (final+1)

esCapicua2:: Integer -> Bool
esCapicua2 n = n == invertirNumero n

--problemas con 1000000 -> 1
invertirNumero :: Integer -> Integer
invertirNumero n
    | cantDigitos n == 1 = n
    | otherwise = (digitoUnidades n)*10^((cantDigitos n)-1) + invertirNumero (eliminarUltimoDigito n)

--Ejercicio 10
{-
problema f1:(n: Z) : Z  {
requiere: {n >= 0}
asegura: {res es la sumatorias de las primeras n+1 potencias de 2}
}
-}
--n = 0 -> 1 ; n = 1 -> 2+1= 3 ; n = 2 -> 4+2+1= 7 ; n = 3 -> 8+4+2+1= 15 ;
--n = 4 -> 16+4+8+2+1= 31; n = 5 -> 32+16+4+8+2+1= 63 ;
f1 :: Integer -> Integer
f1 0 = 2^0
f1 n = 2^n + f1 (n-1)

{-
problema f2:(n: Z, q: R) : R  {
requiere: {n >= 1}
asegura: {res es la sumatorias de las primeras n potencias de q,
        desde q^1 hasta q^n}
}
-}
--q = 3 n=1 -> 3 ; n=2 -> 12 ; n=3 -> 39 ;
--      n=4 -> 120 ; n=5 -> 363 ;
f2 :: Integer -> Float -> Float
f2 1 q = q^1
f2 n q = q^n + f2 (n-1) q

{-
problema f3:(n: Z, q: R) : R  {
requiere: {n >= 1}
asegura: {res es la sumatorias de las primeras 2n potencias de q,
        desde q^1 hasta q^(2n)}
}
-}
f3 :: Integer -> Float -> Float
f3 n q = f2 (2*n) q

{-
problema f4:(n: Z, q: R) : R  {
requiere: {n >= 0 y q /= 0}
asegura: {res es la sumatorias de las primeras n+1 potencias de q,
        desde q^n hasta q^(2n)}
}
-}
--q = 3 n=0 -> 1 ; n=1 -> 12 ; n=2 -> 117 ; n=3 -> 1.080 ; 
--      n=4 -> 9.801 ; n=5 -> 88.452
f4 :: Integer -> Float -> Float
f4 0 _ = 1
f4 1 q = f3 1 q
f4 n q = f3 n q - (f2 (n-1) q)

--Ejercicio 11
{-
problema eAprox: (n: Z) : R {
requiere {n >= 0}
asegura {aproximacion al valor de e}
}
-}
eAprox :: Integer -> Float
eAprox 0 = 1
eAprox n = 1/(fromIntegral (factorial n)) + eAprox (n-1)

{- Definir la constante e como la aproximacion de e
a partir de los primeros 10 terminos de la serie anterior
-}
e :: Float
e = eAprox 10

--Ejercicio 12
{-
problema sucesionSqrtPlusOne (n : Z) : R{
requiere {n >= 1}
asegura {res es el enesimo termino de la sucesion a1 = 2, 2 + 1/a(n-1)}
}
-}
sucesionSqrtPlusOne :: Integer -> Float
sucesionSqrtPlusOne 1 = 2
sucesionSqrtPlusOne n = 2 + 1/sucesionSqrtPlusOne(n-1)

{-
problema raizDe2Aprox (n : Z) : R{
requiere {n >= 1}
asegura {res una aproximacion de la raiz de 2 segun
        el enesimo termino de sucesionSqrtPlusOne}
}
-}
raizDe2Aprox :: Integer -> Float
raizDe2Aprox n = sucesionSqrtPlusOne n

--Ejercicio 13
{-
problema sumatoriaDeSumatoriaDePotencias (n,m : Z) : Z{
requiere {n >= 1 y m >= 1}
asegura {res es la sumatoria de sumatoriaDePotencias}
}
-}
--n = 1 y m = 1 -> 1 ; n = 4 y m = 3 -> 140
sumatoriaDeSumatoriaDePotencias :: Integer -> Integer -> Integer
sumatoriaDeSumatoriaDePotencias 1 m = sumatoriaDePotencias m 1
sumatoriaDeSumatoriaDePotencias n m = sumatoriaDePotencias m n + sumatoriaDeSumatoriaDePotencias (n-1) m

sumatoriaDePotencias :: Integer -> Integer -> Integer
sumatoriaDePotencias 1 n = n
sumatoriaDePotencias m n = n^m + sumatoriaDePotencias (m-1) n

--Ejercicio 14
{-
problema sumaPotencias (q,n,m : Z) : Z{
requiere {a >= 1 y b >= 1}
asegura {res es la sumatoria desde a = 1 hasta n de
        sumaDePotenciasInterna }
}
-}
-- q=3, n=m=2 -> 144
sumaPotencias :: Integer ->Integer ->Integer ->Integer
sumaPotencias q n m = sumaDePotenciasExterna q n m

sumaDePotenciasExterna :: Integer ->Integer ->Integer ->Integer
sumaDePotenciasExterna q 1 m = sumaDePotenciasInterna q 1 m
sumaDePotenciasExterna q n m =  sumaDePotenciasInterna q n m + sumaDePotenciasExterna q (n-1) m

sumaDePotenciasInterna :: Integer ->Integer ->Integer ->Integer
sumaDePotenciasInterna q n 1 = q^(n+1)
sumaDePotenciasInterna q n m = q^(n+m) + sumaDePotenciasInterna q n (m-1)

--Ejercicio 15
{-
problema sumaRacionales (n,m : Z) : Z {
requiere {n >=1 y m >= 1}
asegura {res es la sumatoria de }
}
-}
--n = 3 y m = 3 -> 11 ; n = 4 y m = 3 -> 18.33
sumaRacionales :: Integer -> Integer -> Float
sumaRacionales n m = sumaRacionalesExterna n m

sumaRacionalesExterna :: Integer -> Integer ->Float
sumaRacionalesExterna 1 m = sumaRacionalesInterna 1 m
sumaRacionalesExterna n m =  sumaRacionalesInterna n m + sumaRacionalesExterna (n-1) m

sumaRacionalesInterna :: Integer -> Integer -> Float
sumaRacionalesInterna n 1 = fromIntegral n
sumaRacionalesInterna n m = fromIntegral n/fromIntegral m + sumaRacionalesInterna n (m-1)

--Ejercicio 16
{-
problema menorDivisor (n : Z) : Z{
requiere { n > 1 }
asegura {res es el menor divisor de n, mayor que 1}
-}
menorDivisor :: Integer -> Integer
menorDivisor 1 = 1
menorDivisor n = buscarMenorDivisorMayorAUno n 2

buscarMenorDivisorMayorAUno :: Integer -> Integer -> Integer
buscarMenorDivisorMayorAUno n d
    | mod n d == 0 = d
    | otherwise = buscarMenorDivisorMayorAUno n (d+1)

{-
problema (n : Z) : Bool {
requiere {n > 1}
asegura {res es True si n es primo}
}
-}
esPrimo :: Integer -> Bool
esPrimo n
    | menorDivisor n == n = True
    | otherwise = False

{-
problema sonCoprimos (n,m : Z) : Bool {
requier {n > 1 y m > 1}
asegura {res es True si no n y m no tienen divisor en comun aparte del 1}
}
Algoritmo de Euclides (a:b) = (b:rb(a))
Propiedad: (a:b) = 1 sii a y b son coprimos
-}
sonCoprimos :: Integer -> Integer -> Bool
sonCoprimos n m = euclidesMcd n m == 1

euclidesMcd :: Integer -> Integer -> Integer
euclidesMcd mcd 0 = mcd
euclidesMcd n m 
    | (absoluto m) > (absoluto n) = euclidesMcd m n
    | otherwise = euclidesMcd m (mod n m)

{-
problema nEsimoPrimo (n: Z) : Z {
requier {n >= 1}
asegura {res es el nesimo primo}
}
-}
nEsimoPrimo :: Integer -> Integer
nEsimoPrimo n = ultimo (listaDeLosPrimerosNPrimos n)

listaDeLosPrimerosNPrimos :: Integer -> [Integer]
listaDeLosPrimerosNPrimos n = tail (tomar (n+1) (filtrar (esPrimo) [1..]))

tomar :: Integer -> [a] -> [a]
tomar _ [] = []
tomar 0 _ = []
tomar n (x:xs) = x : tomar (n-1) xs

filtrar :: (a -> Bool) -> [a] -> [a]
filtrar f [] = []
filtrar f (x:xs)
    | f x = x : filtrar f xs
    | otherwise = filtrar f xs

{-
problema ultimo (s: seq⟨T⟩) : T {
requiere: { |s| > 0 }
asegura: { resultado = s[|s| − 1] }
}
-}
ultimo :: [t] -> t
ultimo (x:[]) = x
ultimo (x:xs) = ultimo (xs)


--Ejercicio 17
{-
problema esFibonacci (n: Z) : B {
requiere: { n ≥ 0 }
asegura: { resultado = true ↔ n es algun valor de la secuencia de Fibonacci}
}
-}
esFibonacci :: Integer -> Bool
esFibonacci n = ultimo (listaDeNrosDeFibonacci n) == n

listaDeNrosDeFibonacci :: Integer -> [Integer]
listaDeNrosDeFibonacci n = tomarMientras (<=n) (mapear (fibonacci) [1..])

tomarMientras :: (a -> Bool) -> [a] -> [a]
tomarMientras _ [] = []
tomarMientras f (x:xs)
    | f x =  x : tomarMientras f xs
    | otherwise = []

mapear :: (a -> b) -> [a] -> [b]
mapear _ [] = []
mapear f (x:xs) = f x : mapear f xs

-- Ejercicio 18

{-
mayorDigitoPar :: Integer -> Integer

-}
mayorDigitoPar :: Integer -> Integer
mayorDigitoPar n
    | ultimoDig == parteAnterior && esPar ultimoDig = -1
    | ultimoDig == parteAnterior = -1
    | esPar ultimoDig = esMayor ultimoDig (mayorDigitoPar parteAnterior)
    | otherwise = mayorDigitoPar parteAnterior
    where
        ultimoDig = mod n 10
        parteAnterior = div n 10

esPar :: Integer -> Bool
esPar n = mod n 2 == 0

esMayor :: Integer -> Integer -> Integer
esMayor a b
    | a > b = a
    | otherwise = b


-------
gauss :: Integer -> Integer
gauss 0 = 0
gauss m = m + gauss (m-1)

nEsimoPrimo2 :: Integer -> Integer
nEsimoPrimo2 n = aux n 2 1
    where
        aux n p acc 
            | esPrimo p && acc == n = p
            | esPrimo p && acc < n = aux n (p+1) (acc+1)
            | otherwise = aux n (p+1) acc

esFibonacci2 :: Integer -> Bool
esFibonacci2 n = aux n 0
    where
        aux n acc
            | fibonacci acc < n = aux n (acc+1)
            | fibonacci acc == n = True
            | otherwise = False

---Ejercicio 19
{-esSumaInicialDePrimos :: Integer -> Bool
esSumaInicialDePrimos 
-}
esSumaInicialDePrimos :: Integer -> Bool
esSumaInicialDePrimos n = esSumaInicialDePrimosAux n 1

esSumaInicialDePrimosAux :: Integer -> Integer -> Bool
esSumaInicialDePrimosAux n y
    | sumaDeNPrimos y < n = esSumaInicialDePrimosAux n (y+1)
    | n == sumaDeNPrimos y = True
    | otherwise = False

sumaDeNPrimos :: Integer -> Integer
sumaDeNPrimos n = sumaDeNPrimosAux n 1

sumaDeNPrimosAux :: Integer -> Integer -> Integer
sumaDeNPrimosAux n acc
    | acc < n = nEsimoPrimo2 acc + sumaDeNPrimosAux n (acc+1)
    | acc == n = nEsimoPrimo2 acc


{-
21

f m n r
g Em In r + f m-1 n r

g Em In r
    | Em + In < r^2 = 1 + g m n-1 r
    | otherwise = 0
-}

