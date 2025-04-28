--Ejercicio 1
{-
problema longitud (s: seq<T>) : Z {
requiere {True}
asegura {res = cantidad de elementos de una lista}
}
-}
{-
longitud :: (Eq t) => [t] -> Integer
longitud seq
    | seq == [] = 0
    | otherwise = 1 + longitud (tail seq)
-}
--PM elimina la necesidad de Eq t
longitud :: [t] -> Integer
longitud [] = 0
longitud (_:xs) = 1 + longitud xs

{-
problema ultimo (s: seq⟨T⟩) : T {
requiere: { |s| > 0 }
asegura: { resultado = s[|s| − 1] }
}
-}
ultimo :: [t] -> t
ultimo (x:[]) = x
ultimo (x:xs) = ultimo (xs)

{-
problema principio (s: seq⟨T⟩) : seq⟨T⟩ {
requiere: { |s| > 0 }
asegura: { resultado = subseq(s, 0, |s| − 1) }
}
-}
principio :: [t] -> [t]
principio [x] = []
principio (x:xs) = x:principio xs

{-
problema reverso (s: seq⟨T⟩) : seq⟨T⟩ {
requiere: { True }
asegura: { resultado tiene los mismos elementos que s pero en orden inverso}
}
-}
reverso :: [t] -> [t]
reverso [] = []
reverso [x] = [x]
reverso (x:xs) = reverso xs ++ [x]

final :: [t] -> [t]
final [] = []
final (x:xs) = xs

--Ejercicio 2
{-
problema pertenece (e: T, s: seq⟨T⟩) : B {
requiere: { True }
asegura: { resultado = true ↔ e ∈ s }
}
-}
pertenece :: (Eq t) => t -> [t] -> Bool
pertenece e [] = False
pertenece e (x:xs) = e == x || pertenece e (xs)
{-
pertenece :: (Eq t) => t -> [t] -> Bool
pertenece e [] = False
pertenece e (x:xs)
    | e == x = True
    | otherwise = pertenece e (xs)
-}

{-
problema todosIguales (s: seq<T>) : Bool {
requiere {True}
asegura {res = True sii todos los elementos de una lista son iguales}
}
-}
todosIguales :: (Eq t) => [t] -> Bool
todosIguales [] = True
todosIguales [x] = True
todosIguales (x:y:ys) = x == y && todosIguales (y:ys)

{-
problema todosDistintos (s: seq⟨T⟩) : B {
requiere: { True }
asegura: { resultado = false ↔ existen dos posiciones distintas de s con igual valor }
}
-}

todosDistintos :: (Eq t) => [t] -> Bool
todosDistintos [] = True
todosDistintos [x] = True
todosDistintos (x:xs)
    | pertenece x xs = False
    | otherwise = todosDistintos (xs)

{-
problema hayRepetidos (s: seq⟨T⟩) : B {
requiere: { True }
asegura: { resultado = true ↔ existen almenos 2 posiciones distintas de s con igual valor }
}
-}
hayRepetidos :: (Eq t) => [t] -> Bool
hayRepetidos seq = not (todosDistintos seq)

{-
problema quitar (x: T, s: seq<T>) : seq<T> {
requiere {True}
asegura {dados un entero x y una lista xs,
        elimina la primera aparicion de x en
        la lista xs (de haberla).}
}
-}
quitar :: (Eq t) => t -> [t] -> [t]
quitar x [] = []
quitar x (y:ys)
    | x == y = ys
    | x /= y = y : quitar x ys

{-
problema quitarTodos (e: T, s: seq⟨T⟩) : seq⟨T⟩ {
requiere: { True }
asegura: { resultado es igual a s pero sin el elemento e, es decir
        elimina todas las apariciones de e en s (de haberlas)}
}
-}
quitarTodos :: (Eq t) => t -> [t] -> [t]
quitarTodos x xs
    | pertenece x xs = quitarTodos x (quitar x xs)
    | otherwise = xs

{-
problema eliminarRepetidos (s: seq<T>) : seq<T> {
requiere {True}
asegura {res es una lista con una unica aparicion de cada elemento,
        eliminando las repeticiones adicionales}
}
-}
eliminarRepetidos :: (Eq t) => [t] -> [t]
eliminarRepetidos [] = []
eliminarRepetidos [x] = [x]
eliminarRepetidos (x:xs) = x : eliminarRepetidos (quitarTodos x xs)

{-
problema mismosElementos (s: seq⟨T⟩, r: seq⟨T⟩) : B {
requiere: { True }
asegura: { resultado = true ↔ todo elemento de s pertenece r y viceversa,
            sin tener en cuenta repeticiones}
}
-}
mismosElementos :: (Eq t) => [t] -> [t] -> Bool
mismosElementos seq1 seq2
    | longitud (eliminarRepetidos seq1) == longitud (eliminarRepetidos seq2) =
        comparacionDeListasSinRepetidos (eliminarRepetidos seq1)  (eliminarRepetidos seq2)
    | otherwise = False

{-
Compara 2 listas, c/u sin elementos repetidos, y dice si tienen los mismos elementos
-}
comparacionDeListasSinRepetidos :: (Eq t) => [t] -> [t] -> Bool
comparacionDeListasSinRepetidos [] lista2 = True
comparacionDeListasSinRepetidos (x:xs) lista2
    | pertenece x lista2 = comparacionDeListasSinRepetidos xs lista2
    | otherwise = False

{-
problema capicua (s: seq⟨T⟩) : B {
requiere: { True }
asegura: { (resultado = true) ↔ (s = reverso(s)) }
}
-}
capicua :: (Eq t) => [t] -> Bool
capicua seq = seq == reverso seq

--Ejercicio 3
{-
problema sumatoria (s: seq⟨Z⟩) : Z {
requiere: { True }
asegura: { resultado = sumatoria de todos los elementos de la lista }
}
-}
--sumatoria :: [Integer] -> Integer
sumatoria :: Num a => [a] -> a
sumatoria [] = 0
sumatoria (x:xs) = x + sumatoria xs

{-
problema productoria (s: seq⟨Z⟩) : Z {
requiere: { True }
asegura: { resultado = multiplicaion de todos los elementos de la lista entre si }
}
}
-}
productoria :: [Integer] -> Integer
productoria [] = 0
productoria [x] = x
productoria (x:xs) = x * productoria xs

{-
problema maximo (s: seq⟨Z⟩) : Z {
requiere: { |s| > 0 }
asegura: { resultado ∈ s ∧ todo elemento de s es menor o igual a resultado }
}
-}
maximo :: [Integer] -> Integer
maximo [x] = x
maximo (x:y:ys)
    | x >= y = maximo (x:ys)
    | x < y = maximo (y:ys)

{-
problema sumarN (n: Z, s: seq⟨Z⟩) : seq⟨Z⟩ {
requiere: { True }
asegura: {|resultado| = |s| ∧ cada posicion de resultado
        contiene el valor que hay en esa posicion en s sumado n }
}
-}
sumarN :: Integer -> [Integer] -> [Integer]
sumarN n [] = []
sumarN n (x:xs) = x+n : sumarN n xs

--sumarN :: Integer -> [Integer] -> [Integer]
--sumarN n seq = mapear (+n) seq

{-
problema sumarElPrimero (s: seq⟨Z⟩) : seq⟨Z⟩ {
requiere: { |s| > 0 }
asegura: {resultado = sumarN(s[0], s) }
}
-}
sumarElPrimero :: [Integer] -> [Integer]
sumarElPrimero (x:xs) = sumarN x (x:xs)
--sumarElPrimero seq@(x:xs) = sumarN x seq

{-
problema sumarElUltimo (s: seq⟨Z⟩) : seq⟨Z⟩ {
requiere: { |s| > 0 }
asegura: {resultado = sumarN(s[|s| − 1], s) }
}
-}
sumarElUltimo :: [Integer] -> [Integer]
sumarElUltimo seq = sumarN (ultimo seq) seq

{-
problema pares (s: seq⟨Z⟩) : seq⟨Z⟩ {
requiere: { True }
asegura: {resultado solo tiene los elementos pares de s
        en el orden dado, respetando las repeticiones}
}
-}
pares :: [Integer] -> [Integer]
pares [] = []
pares (x:xs)
    | mod x 2 == 0 = x : pares xs
    | otherwise = pares xs
--pares (x:xs) = filtrar (\x -> mod x 2 == 0) (x:xs)

{-
problema multiplosDeN (n: Z, s: seq<Z>) : seq<Z>
requiere {True}
asegura {res contiene los elementos de s que son multiplos de n
        en el orden dado, respetando las repeticiones}
-}
multiplosDeN :: Integer -> [Integer] -> [Integer]
multiplosDeN n [] = []
multiplosDeN n (x:xs)
    | mod x n == 0 = x : multiplosDeN n xs
    | otherwise = multiplosDeN n xs
--multiplosDeN n (x:xs) = filtrar (\x -> mod x n == 0) (x:xs)

{-
problema ordenar (s: seq<Z>) : seq<Z> {
requiere {True}
asegura {res es una lista cuyos elementos esta ordenados en forma creciente}
}
-}
ordenar :: [Integer] -> [Integer]
ordenar xs = reverso $ ordenarDeMayorAMenor xs

ordenarDeMayorAMenor :: [Integer] -> [Integer]
ordenarDeMayorAMenor [] = []
ordenarDeMayorAMenor seq = maximo seq : ordenarDeMayorAMenor (quitar (maximo seq) seq)

ordenarDeMenorAMayor :: [Integer] -> [Integer]
ordenarDeMenorAMayor [] = []
ordenarDeMenorAMayor seq = ordenarDeMenorAMayor (quitar (maximo seq) seq) ++ [maximo seq]

{-
ordenar :: [Integer] -> [Integer]
ordenar [] = []
ordenar (x:xs) =
    let menoresOrdenados = ordenar (filtrar (x >) xs)
        mayoresOrdenados = ordenar (filtrar (x <) xs)
    in menoresOrdenados ++ [x] ++ mayoresOrdenados
-}

--Ejercicio 4
{-
problema sacarBlancosRepetidos (s: seq<Char>) : seq<Char> {
requiere {True}
asegura { reemplaza cada subsecuencia de blancos contiguos de
    la primera lista por un solo blanco en la lista resultado}
}
-}
sacarBlancosRepetidos :: [Char] -> [Char]
sacarBlancosRepetidos [] = []
sacarBlancosRepetidos [x] = [x]
sacarBlancosRepetidos (x:y:ys)
    | x == ' ' && y == ' ' = sacarBlancosRepetidos (y:ys)
    | otherwise = x : sacarBlancosRepetidos (y:ys)

eliminarBlancosDelInicio :: [Char] -> [Char]
eliminarBlancosDelInicio [] = []
eliminarBlancosDelInicio (x:xs)
    | x == ' ' = eliminarBlancosDelInicio xs
    | otherwise = (x:xs)

eliminarBlancosDelFinal :: [Char] -> [Char]
eliminarBlancosDelFinal [] = []
eliminarBlancosDelFinal xs
    | ultimo xs == ' ' = eliminarBlancosDelFinal (principio xs)
    | otherwise = xs

eliminarBlancosInicioFinalRepetidos :: [Char] -> [Char]
eliminarBlancosInicioFinalRepetidos xs = sacarBlancosRepetidos (eliminarBlancosDelInicio (eliminarBlancosDelFinal xs))

{-
problema contarPalabras (s: seq<Char>) : seq<Char> {
requiere {True}
asegura {devuelve la cantidad de palabras que tiene una lista de caracteres,
    entendiendo como palabra todos los caracteres entre 2 Blancos o
    entre el principio y el primer Blanco o
    entre el ultimo Blanco y el final}
}
-}
contarPalabras :: [Char] -> Integer
contarPalabras xs = (contarBlancos (eliminarBlancosInicioFinalRepetidos xs)) + 1
--contarPalabras xs = (contarBlancos $ eliminarBlancosInicioFinalRepetidos xs) + 1
--contarPalabras xs = (contarBlancos (sacarBlancosRepetidos (eliminarBlancosDelInicio (eliminarBlancosDelFinal xs)))) + 1

{-
problema contarBlancos(s: seq<Char>) : seq<Char>{
requier {True}
asegura {res = cantidad de Blancos en la lista}
}
-}
contarBlancos :: [Char] -> Integer
contarBlancos [] = 0
contarBlancos (x:xs)
    | x == ' ' = 1 + contarBlancos (xs)
    | otherwise = contarBlancos (xs)

{-
problema palabra(s: seq<Char>) : seq<seq<Char>> {
requiere {True}
asegura {devuelve una lista en la que cada elemento es
        una palabras de la lista original}
}
-}
palabras :: [Char] -> [[Char]]
palabras [] = []
palabras xs = primeraPalabra (eliminarBlancosInicioFinalRepetidos xs) :
              palabras (eliminarPrimeraPalabra (eliminarBlancosInicioFinalRepetidos xs))

primeraPalabra :: [Char] -> [Char]
primeraPalabra [] = []
primeraPalabra (x:xs)
    | x == ' ' = []
    | otherwise = x : primeraPalabra xs

eliminarPrimeraPalabra :: [Char] -> [Char]
eliminarPrimeraPalabra [] = []
eliminarPrimeraPalabra (x:xs)
    | x == ' ' = xs
    | otherwise = eliminarPrimeraPalabra xs

segundaPalabra :: [Char] -> [Char]
segundaPalabra [] = []
segundaPalabra xs = primeraPalabra (eliminarPrimeraPalabra xs)

eliminarPrimeraYSegundaPalabra :: [Char] -> [Char]
eliminarPrimeraYSegundaPalabra [] = []
eliminarPrimeraYSegundaPalabra (x:xs) = eliminarPrimeraPalabra (eliminarPrimeraPalabra xs)

{-
problema palabraMasLarga(s: seq<Char>) : seq<Char>{
requiere  {True}
asegura {Devuelve la primer palabra mas larga de una lista de caracteres}
}
-}
palabraMasLarga :: [Char] -> [Char]
palabraMasLarga [] = []
palabraMasLarga xs = buscarElementoMasLargo (palabras xs)

buscarElementoMasLargo :: [[a]] -> [a]
buscarElementoMasLargo [x] = x
buscarElementoMasLargo (x:y:ys)
    | longitud x >= longitud y = buscarElementoMasLargo (x:ys)
    | otherwise = buscarElementoMasLargo (y:ys)

{-
problema aplanar (s: seq<seq<Char>>) : seq<Char>{
requier {}
asegura {a partir de una lista de palabras devuelve
        una lista de caracteres concatenandolas}
}
-}
aplanar :: [[Char]] -> [Char]
aplanar [] = []
aplanar (x:xs) = x ++ aplanar xs

{-
problema aplanarConBlancos(s: seq<seq<Char>>) : seq<Char> {
requiere {True}
asegura {lista de caracteres con un blanco entre cada palabas}
}
-}
aplanarConBlancos :: [[Char]] -> [Char]
aplanarConBlancos [] = []
aplanarConBlancos [x] = x
aplanarConBlancos (x:xs) = x ++ " " ++ aplanarConBlancos xs

{-
problema aplanarConNBlancos(s: seq<seq<Char>>, n: Z) : seq<Char>{
requiere { n >= 0 }
asegura {lista de caracteres con n blancos entre cada palabas}
}
-}
aplanarConNBlancos :: [[Char]] -> Integer -> [Char]
aplanarConNBlancos [x] _ = x
aplanarConNBlancos (x:xs) n = x ++ blanco n ++ aplanarConNBlancos xs n
                        where blanco 0 = ""
                              blanco n = " " ++ blanco (n-1)
{-
blanco :: Integer -> [Char]
blanco 0 = ""
blanco n = " " ++ blanco (n-1)
-}

--Ejercicio 5
{-
problema sumaAcumulada (s: seq⟨T⟩) : seq⟨T⟩ {
requiere: {T es un tipo numerico}
requiere: {cada elemento de s es mayor estricto que cero}
asegura: {|s| = |resultado| ∧ el valor en la posicion i de resultado
        de la sumatoria de todos los valores de las posiciones anterioes}
}
-}
sumaAcumulada :: (Num t) => [t] -> [t]
sumaAcumulada [] = []
sumaAcumulada [x] = [x]
sumaAcumulada xs = sumaAcumulada (principio xs) ++ [sumatoria xs]

--Ejercicio 6
type Texto = [Char]
type Nombre = Texto
type Telefono = Texto
type Contacto = (Nombre, Telefono)
type ContactosTel = [Contacto]

--devuelve el nombre de un contactos
elNombre :: Contacto -> Nombre
elNombre (nombre, telefono) = nombre

--devuelve el telefono de un contactos
elTelefono :: Contacto -> Nombre
elTelefono (nombre, telefono) = telefono

{-
problema enLosContactos(s: seq<Char>, q: seq< seq<Char> X seq<Char> >) : Bool {
requiere {True}
asegura {res = True si una persona aparece en la lista de contactos del telefono}
} 
agenda = [("ana", "1111"),("belen", "2222"),("carlos", "3333"),("dardo", "4444")]
-}
enLosContactos :: Nombre -> ContactosTel -> Bool
enLosContactos nombre [] = False
enLosContactos nombre agenda
    | nombre == elNombre (head agenda) = True
    | otherwise = enLosContactos nombre (tail agenda)

{-
problema agregarContacto(d: seq<Char> X seq<Char>, s: seq< seq<Char> X seq<Char> >) : seq< seq<Char> X seq<Char> >{
requiere {True}
asegura {agrega una nueva persona a mis contactos}
asegura {si la persona ya existe en mis contactos entonces actuazliza el telefono}
}
agregarContacto :: Contacto -> ContactosTel -> ContactosTel
agregarContacto contacto@(nombre,telefono) agenda
    | enLosContactos nombre agenda = actualizarContacto contacto agenda
    | otherwise = agenda ++ [contacto]
-}
agregarContacto :: Contacto -> ContactosTel -> ContactosTel
agregarContacto (nombre,telefono) agenda
    | enLosContactos nombre agenda = actualizarContacto (nombre,telefono) agenda
    | otherwise = agenda ++ [(nombre,telefono)]

actualizarContacto :: Contacto -> ContactosTel -> ContactosTel
actualizarContacto (nombre,telefono) [] = []
actualizarContacto (nombre,telefono) (contacto:contactos)
    | nombre == elNombre contacto = (nombre,telefono) : actualizarContacto (nombre,telefono) contactos
    | otherwise = contacto : actualizarContacto (nombre,telefono) contactos

{-
problema eliminarContacto(s: seq<Char>, s: seq< seq<Char> X seq<Char> >) : seq< seq<Char> X seq<Char> >{
requiere {True}
asegura {elimina un contacto existente de la agenda de contactos}
-}
eliminarContacto :: Nombre -> ContactosTel ->ContactosTel
eliminarContacto nombre agenda
    | enLosContactos nombre agenda = eliminarUnContacto nombre agenda
    | otherwise = agenda

eliminarUnContacto  :: Nombre -> ContactosTel -> ContactosTel
eliminarUnContacto nombre [] = []
eliminarUnContacto nombre (contacto:contactos)
    | nombre == elNombre contacto = eliminarUnContacto nombre contactos
    | otherwise = contacto : eliminarUnContacto nombre contactos

--Ejercicio 7
type Disponibilidad = Bool
type Ubicacion = Texto
type Identificacion = Integer
type Estado = (Disponibilidad, Ubicacion) --      (False,"ZD39I")
type Locker = (Identificacion, Estado) -- ( 100 , (False,"ZD39I") )
type MapaDeLockers = [Locker]

casilleros =
    [
    (100,(False,"ZD39I")),
    (101,(True,"JAH3I")),
    (103,(True,"IQSA9")),
    (105,(True,"QOTSA")),
    (109,(False,"893JJ")),
    (110,(False,"99292"))
    ]

{-
problema existeElLocker( ) : {
requiere {}
asegura { True si un locker existe en la facultad } 
}
-}
existeElLocker :: Identificacion -> MapaDeLockers -> Bool
existeElLocker id [] = False
existeElLocker id (locker:lockers)
    | id == fst locker = True
    | otherwise = existeElLocker id lockers

{-
problema ubicacionDelLocker( ) : {
requiere {}
asegura { dado un locker que existe en la facultad, me dice la ubicacion del mismo }
}
-}
ubicacionDelLocker :: Identificacion -> MapaDeLockers -> Ubicacion
ubicacionDelLocker id [] = "No existe ese locker"
ubicacionDelLocker id (locker:lockers)
    | id == fst locker = snd (snd locker)
    | otherwise = ubicacionDelLocker id lockers

{-
problema estaDisponibleElLocker( ) : {
requiere {}
asegura { dado un locker que existe en la facultad, me devuelve Verdadero si esta libre }
}
-}
estaDisponibleElLocker :: Identificacion -> MapaDeLockers -> Bool
estaDisponibleElLocker id (locker:lockers)
    | id == fst locker = fst (snd locker)
    | otherwise = estaDisponibleElLocker id lockers

{-
problema ocuparLocker( ) : {
requiere {}
asegura { dado un locker que existe en la facultad, y esta libre, lo ocupa }
}
-}
ocuparLocker :: Identificacion -> MapaDeLockers -> MapaDeLockers
ocuparLocker id  [] = []
ocuparLocker id (locker:lockers)
    | id == fst locker && fst (snd locker) == False =
        cambiarEstadoLocker locker : ocuparLocker id lockers
    | otherwise = locker : ocuparLocker id lockers

cambiarEstadoLocker :: Locker -> Locker
cambiarEstadoLocker (id, (disp, ubi)) = (id, (not disp, ubi))


------------
------------
mapear :: (a -> b) -> [a] -> [b]
mapear f [] = []
mapear f (x:xs) = f x : mapear f xs

comprimirCon :: (a -> b -> c) -> [a] -> [b] -> [c]
comprimirCon f _ [] = []
comprimirCon f [] _ = []
comprimirCon f (x:xs) (y:ys) = f x y : comprimirCon f xs ys

filtrar :: (a -> Bool) -> [a] -> [a]
filtrar f [] = []
filtrar f (x:xs)
    | f x = x : filtrar f xs
    | otherwise = filtrar f xs

