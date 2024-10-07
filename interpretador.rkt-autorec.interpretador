#lang eopl

;;* Estudiantes:
;;* Elkin Samir Angulo Panameño (2240578)
;;* Leonardo Cuadro Lopez (2241951)

#|
? Valores denotados: Texto + Número + Booleano + ProcVal
? Valores expresado: Texto + Número + Booleano + ProcVal

!<programa>  :=  <expresion> un-programa (exp)

!<expresion> := <numero> numero-lit (num)
!            := "\""<texto> "\"" texto-lit (txt)
!            := <identificador> var-exp (id)
!            := (<expresion> <primitiva-binaria> <expresion>) primapp-bin-exp (exp1 prim-binaria exp2)
!            := <primitiva-unaria> (<expresion>) primapp-un-exp (prim-unaria exp)

!<primitiva-binaria> :=  + (primitiva-suma)
!	                   :=  ~ (primitiva-resta)
!	                   :=  / (primitiva-div)
!	                   :=  * (primitiva-multi)
!	                   :=  concat (primitiva-concat)
!                    := > (primitiva-mayor)
!                    := < (primitiva-menor)
!                    := >= (primitiva-mayor-igual)
!                    := <= (primitiva-menor-igual)
!                    := != (primitiva-diferente)
!                    := == (primitiva-comparador-igual)

!<primitiva-unaria>  :=  longitud (primitiva-longitud)
!                    :=  add1 (primitiva-add1)
!                    :=  sub1 (primitiva-sub1)
!                    :=  neg (primitiva-negacion-booleana)
|#

;******************************************************************************
;* Especificación Léxica

(define especificacion-interpretador-simple
  '((espacio-en-blanco
     (whitespace) skip) ; Espacios en blanco
    (comentario
     ("//" (arbno (not #\newline))) skip) ; Comentarios
    (identificador
     ("@" letter (arbno (or letter digit))) symbol) ; Definición de identificadores
    (numero
     (digit (arbno digit)) number) ; Enteros positivos
    (numero
     ("-" digit (arbno digit)) number) ; Enteros negativos
    (numero
     (digit (arbno digit) "." digit (arbno digit)) number) ; Decimales positivos
    (numero
     ("-" digit (arbno digit) "." digit (arbno digit)) number) ; Decimales negativos
    (texto
     ( letter (arbno (or letter digit "_" ":"))) string)) ; Definción de texto
  )

;*********************************************************************************
;* Especificación Sintáctica (gramática)

(define gramatica-interpretador-simple
  '((programa (expresion) un-programa)
    (expresion (numero) numero-lit)
    (expresion (identificador) var-exp)
    (expresion ("\"" texto "\"") texto-lit)
    (expresion (primitiva-unaria "(" expresion ")") primapp-un-exp)
    (expresion ("(" expresion primitiva-binaria expresion ")") primapp-bin-exp)
    (expresion ("Si"  expresion  "{" expresion "}" "sino" "{" expresion "}") condicional-exp)
    (expresion ("declarar" "(" (arbno identificador "=" expresion ";") ")"  "{" expresion "}") variableLocal-exp)
    (expresion ("declarar-recursivamente"  "(" "[" (arbno identificador "(" (separated-list identificador ",") ")"  "=" expresion ";") "]" ")" "{" expresion "}" ) variableRecursiva-exp)
    (expresion ("procedimiento" "(" (separated-list identificador ",") ")" "{" expresion "}") procedimiento-ex)
    (expresion ("evaluar" expresion "(" (separated-list expresion ",") ")" "finEval") app-exp)

    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("~") primitiva-resta)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("concat") primitiva-concat)
    (primitiva-binaria (">") primitiva-mayor)
    (primitiva-binaria ("<") primitiva-menor)
    (primitiva-binaria (">=") primitiva-mayor-igual)
    (primitiva-binaria ("<=") primitiva-menor-igual)
    (primitiva-binaria ("!=") primitiva-diferente)
    (primitiva-binaria ("==") primitiva-comparador-igual)

    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
    (primitiva-unaria ("neg") primitiva-negacion-booleana)
    ))

;*********************************************************************************
;* Contruyendo datatypes
(sllgen:make-define-datatypes especificacion-interpretador-simple gramatica-interpretador-simple)

(define mostrar-datatypes
  (lambda () (sllgen:list-define-datatypes especificacion-interpretador-simple gramatica-interpretador-simple)))

;* Parser, Scanner e Interfaz
(define escanea&parsea
  (sllgen:make-string-parser especificacion-interpretador-simple gramatica-interpretador-simple))

(define escaner
  (sllgen:make-string-scanner especificacion-interpretador-simple gramatica-interpretador-simple))

(define interpretador
  (sllgen:make-rep-loop "--> "
                        (lambda (programa) (evaluar-programa programa))
                        (sllgen:make-stream-parser
                         especificacion-interpretador-simple
                         gramatica-interpretador-simple)))

;***********************************************************************************
;* Intérprete

; evaluar-programa: Exp -> Exp*

(define evaluar-programa
  (lambda (parametro-programa)
    (cases programa parametro-programa
      (un-programa (una-expresion)
                   (evaluar-expresion una-expresion (ambiente-inicial)))
      )
    ))

; evaluar-expresión: Exp x Amb ->

(define evaluar-expresion
  (lambda (una-expresion un-ambiente)
    (cases expresion una-expresion
      (numero-lit (num) num)
      (var-exp (id) (buscar-variable un-ambiente id))
      (texto-lit (txt) txt)
      (primapp-bin-exp (exp1 prim-binaria exp2)
                       (evaluar-primitiva-binaria
                        prim-binaria
                        (evaluar-operadores (list exp1 exp2) un-ambiente)))
      (primapp-un-exp (prim-unaria exp)
                      (evaluar-primitiva-unaria
                       prim-unaria (evaluar-expresion exp un-ambiente)))
      (condicional-exp (test-exp true-exp false-exp)
                       (if (valor-verdadero? (evaluar-expresion test-exp un-ambiente))
                           (evaluar-expresion true-exp un-ambiente)
                           (evaluar-expresion false-exp un-ambiente)))
      (variableLocal-exp (ids exps cuerpo)
                         (let
                             (( valores (evaluar-operadores exps un-ambiente)))
                           (evaluar-expresion cuerpo (ambiente-extendido ids valores un-ambiente))))
      (procedimiento-ex (ids cuerpo)
                        (cerradura ids cuerpo un-ambiente))
      (app-exp (exp exps)
               (let
                   ((procedimiento (evaluar-expresion exp un-ambiente))
                    (argumentos (evaluar-operadores exps un-ambiente)))
                 (if (procVal? procedimiento)
                     (evaluar-procedimiento procedimiento argumentos)
                     (" Error al evaluar un procedimiento inválido ~s 🙀" procedimiento)
                     )))
      (variableRecursiva-exp (nombres-proc parametros expresiones-recursivas cuerpo)
                             (evaluar-expresion cuerpo (ambiente-extendido-recursivamente
                                                        nombres-proc
                                                        parametros
                                                        expresiones-recursivas
                                                        un-ambiente)))
      )))

(define evaluar-primitiva-unaria
  (lambda (primitiva un-valor)
    (cases primitiva-unaria primitiva
      (primitiva-longitud () (string-length un-valor))
      (primitiva-add1 () (+ un-valor 1))
      (primitiva-sub1 () (- un-valor 1))
      (primitiva-negacion-booleana () (verdadero-falso? (not (valor-verdadero? un-valor))))
      )
    ))

(define evaluar-primitiva-binaria
  (lambda (primitiva valores)
    (cases primitiva-binaria primitiva
      (primitiva-suma () (+ (car valores) (cadr valores)))
      (primitiva-resta () (- (car valores) (cadr valores)))
      (primitiva-multi () (* (car valores) (cadr valores)))
      (primitiva-div () (/ (car valores) (cadr valores)))
      (primitiva-concat () (string-append (car valores) (cadr valores)))
      (primitiva-mayor () (verdadero-falso? (> (car valores) (cadr valores))))
      (primitiva-menor () (verdadero-falso? (< (car valores) (cadr valores))))
      (primitiva-mayor-igual () (verdadero-falso? (>= (car valores) (cadr valores))))
      (primitiva-menor-igual () (verdadero-falso? (<= (car valores) (cadr valores))))
      (primitiva-diferente () (verdadero-falso? (not (equal? (car valores) (cadr valores)))))
      (primitiva-comparador-igual () (verdadero-falso? (equal? (car valores) (cadr valores))))
      )
    ))

;***********************************************************************************
;* Ambientes

;* Ambiente inicial
(define ambiente-inicial
  (lambda ()
    (ambiente-extendido
     '(@a @b @c @d @e)
     '( 1  2  3  "hola" "FLP")
     (ambiente-vacio)
     )
    ))

(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido
   (nombres-identificadores (list-of symbol?))
   (valores-variables (list-of valor-scheme?))
   (ambiente ambiente?)
   )
  (ambiente-extendido-recursivamente
   (nombres-procedimientos (list-of symbol?))
   (identificadores (list-of (list-of symbol?)))
   (expresiones-recursivas (list-of expresion?))
   (ambiente-anterior ambiente?))
  )

(define buscar-variable
  (lambda (parametro-ambiente identificador)
    (cases ambiente parametro-ambiente
      (ambiente-vacio () (eopl:error 'ambiente-vacio "La variable ~s no existe 🙀" identificador))
      (ambiente-extendido (nombres-identificadores valores-variables ambiente-anterior)
                          (let
                              ((posicion (buscar-posicion identificador nombres-identificadores)))
                            (if (number? posicion)
                                (list-ref valores-variables posicion)
                                (buscar-variable ambiente-anterior identificador))))

      (ambiente-extendido-recursivamente (nombres-proc parametros expresiones-recursivas ambiente-anterior)
                                         (let
                                             ((posicion (buscar-posicion identificador nombres-proc)))
                                           (if (number? posicion)
                                               (cerradura
                                                (list-ref parametros posicion)
                                                (list-ref expresiones-recursivas posicion)
                                                parametro-ambiente)
                                               (buscar-variable ambiente-anterior identificador))
                                           ))
      )
    ))

;*****************************************************************************************************
;;* BOOLEANOS

;* Cualquier valor es verdadero menos el cero.
(define valor-verdadero?
  (lambda (x) (not (zero? x))))

(define valor-scheme? (lambda (v) #t))

(define verdadero-falso?
  (lambda (x) (if (equal? x #t) 1 0)))


;*****************************************************************************************************
;* Cerradura (Closure)

;! Aplicarlo en el evaluar-expresion
(define-datatype procVal procVal?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expresion?)
   (amb ambiente?)
   )
  )

(define evaluar-procedimiento
  (lambda (procedimiento argumentos)
    (cases procVal procedimiento
      (cerradura (lista-ID exp amb)
                 (evaluar-expresion exp (ambiente-extendido lista-ID argumentos amb))))))

;*****************************************************************************************************
;;* FUNCIONES AUXILIARES
;* Creando función para buscar posición

(define buscar-posicion
  (lambda (identificador nombres-identificadores)
    (hallar-indice (lambda (symbolo) (eqv? symbolo identificador)) nombres-identificadores)
    ))

(define hallar-indice
  (lambda (predicado lista)
    (cond
      [(null? lista) #f]
      [(predicado (car lista)) 0]
      [else
       (let
           ((hallar-indice-r (hallar-indice predicado (cdr lista))))
         (if (number? hallar-indice-r)
             (+ hallar-indice-r 1)
             #f
             )
         )
       ]
      )
    ))

(define evaluar-operadores
  (lambda (operadores un-ambiente)
    (map (lambda (operador)
           (evaluar-expresion operador un-ambiente))
         operadores)))


;*****************************************************************************************************
;* Pruebas

#|
  // a)
 declarar-recursivamente([
  // divisionEntera: numero-lit x numero-lit -> numero-lit
  // propósito: Calcular la división entera de dos números
  // uso: evaluar @divisionEntera(10, 3) finEval => 3
   @divisionEntera(@x, @y) = Si (@x < @y) { 0 } sino { (1 + evaluar @divisionEntera((@x ~ @y), @y) finEval) };
  // sumarDigitos: numero-lit -> numero-lit
  // propósito: Sumar los dígitos de un número
  // uso: evaluar @sumarDigitos(147) finEval => 12
   @sumarDigitos(@numero) = 
              Si (@numero == 0) { 0 } 
              sino { 
                ((@numero ~ (evaluar @divisionEntera(@numero, 10) finEval * 10)) + evaluar @sumarDigitos(evaluar @divisionEntera(@numero, 10) finEval) finEval)
              };
   ]) {
        evaluar @sumarDigitos(147) finEval
   }

  // b)
  declarar-recursivamente ([
    // factorial: numero-lit -> numero-lit
    // propósito: Calcular el factorial de un número
    // uso: evaluar @factorial(5) finEval => 120
   @factorial(@x)= Si (@x == 0) { 1 } sino { (@x * evaluar @factorial(sub1(@x)) finEval)};
  ]) { evaluar @factorial(5) finEval }

  declarar-recursivamente ([
    @factorial(@x, @y)= Si (@x == 0) { 1 } sino { (@x * evaluar @factorial(sub1(@x)) finEval)};
  ]) { evaluar @factorial(10) finEval }

  // c)
  declarar-recursivamente([
    // potencia: numero-lit x numero-lit -> numero-lit
    // propósito: Calcular la potencia de un número
    // uso: evaluar @potencia(4, 2) finEval => 16
    @potencia(@base, @exponente) = 
     Si (@exponente == 0) { 
       1 
     } sino { 
       (@base * evaluar @potencia(@base, sub1(@exponente)) finEval) 
     };
    ]) {
      evaluar @potencia(4, 2) finEval
    }

  // d)
  declarar-recursivamente([
    // sumaRango: numero-lit x numero-lit -> numero-lit
    // propósito: Calcular la suma de los números en un rango
    // uso: evaluar @sumaRango(2, 5) finEval => 14
   @sumaRango(@a, @b) = 
     Si (@a == @b) { 
       @b 
     } sino { 
       (@a + evaluar @sumaRango(add1(@a), @b) finEval) 
     };
    ]) { evaluar @sumaRango(2, 5) finEval }
  
  // e)
  declarar (
    // integrantes: -> texto.lit
    // propósito: Devolver el nombre de los integrantes del taller
    // uso: evaluar @integrantes() finEval => "Elkin_y_Leonardo_"
    @integrantes = procedimiento () { "Elkin_y_Leonardo" };  
    // saludar: procedimiento-exp -> texto.lit
    // propósito: Concatenar un saludo con el resultado de un procedimiento
    // uso: evaluar @saludar(@integrantes) finEval => "Hola: Elkin_y_Leonardo_"
    @saludar = procedimiento (@proc) { procedimiento () { ("Hola:_" concat evaluar @proc() finEval) } };
  ) {
  declarar(
    // decorate: -> texto.lit
    // propósito: Decorar un saludo
    // uso: evaluar @decorate() finEval => "Hola: Elkin_y_Leonardo_"
    @decorate = evaluar @saludar(@integrantes) finEval;
  ) { evaluar @decorate() finEval } }

  // f)
  declarar (
    // integrantes: -> texto.lit
    // propósito: Devolver el nombre de los integrantes del taller
    // uso: evaluar @integrantes() finEval => "Elkin_y_Leonardo_"
    @integrantes = procedimiento () { "Elkin_y_Leonardo_" };  
    // saludar: procedimiento-exp -> texto.lit
    // propósito: Concatenar un saludo con el resultado de un procedimiento
    // uso: evaluar @saludar(@integrantes) finEval => "Hola: Elkin_y_Leonardo_"
    @saludar = procedimiento (@proc) { procedimiento() { ("Hola:_" concat evaluar @proc() finEval) }};
  ) {
  declarar(
    // decorate: -> texto.lit -> texto.lit
    // propósito: Decorar un saludo con un texto adicional pasado como parámetro
    // uso: evaluar @decorate("EstudiantesFLP") finEval => "Hola: Elkin_y_Leonardo_EstudiantesFLP"
    @decorate = procedimiento (@texto) { (evaluar evaluar @saludar(@integrantes) finEval () finEval concat @texto)  };
  ) { evaluar @decorate("EstudiantesFLP") finEval } }
|#

(interpretador)