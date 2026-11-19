# Referencia del lenguaje Formal (`.res`)

Esta página enumera cada construcción del lenguaje Formal con un ejemplo
mínimo, qué significa y qué orden la evalúa. Cada bloque `res` es un módulo
completo: el test `language_reference_examples_elaborate`
(`src/language_reference_tests.rs`) extrae todos los bloques de esta página y
comprueba que se analizan y elaboran. Las salidas citadas se obtuvieron
ejecutando el bloque con el launcher.

El pipeline activo es Formal → SurfaceAST → TypedAST → derivación/runtime. El
frontend CNL está conservado y pausado.

## Ejecutar un fichero

Siempre mediante el launcher o el runner, que imponen los límites de memoria y
tiempo ([AGENTS.md](../AGENTS.md)):

| Orden | Qué hace |
|---|---|
| `./residuum run f.res` | Cierre hacia delante: todo lo derivable y si se cumple cada objetivo |
| `./residuum query f.res` | La consulta declarada en cada experimento (residual, residual activa o FOUR) |
| `./residuum explain f.res` | Justificaciones del cierre y selección de defaults |
| `./residuum execute f.res` | Como `run`, y aplica los efectos derivados al `state` de cada experimento |
| `--steps N`, `--trace` | Evaluación por pasos (1..4096) o mostrando cada paso |

`python3 scripts/test_safe.py --fixture f.res` ejecuta el runner de fixtures,
con `--forward` (cierre con programas activos) o `--incremental` (compara los
experimentos `base` y `delta`; `--library lib.res` añade declaraciones
compartidas).

## Módulo y ficheros

```res
// Un comentario de línea.
module Minimal

entity Person
const juan : Person
```

Un fichero puede importar declaraciones de otro, con una ruta relativa a él;
no se importan sus experimentos:

```text
import "../legal/give_formal.res"
```

Límites: 64 KiB por fichero raíz, 1 MiB y 64 módulos sumando los imports.

## Tipos y valores

```res
module Types

entity Thing
entity Person {
    assets : Set Thing
}
entity Buyer <: Person
entity Slot {
    first : PropositionTime
    second : PropositionTime
}

const ana : Buyer
const car : Thing
const tau : PropositionTime

derived verb reserved(slot : Slot, extra : Thing?)

experiment values {
    premises {
        reserved(Slot { second = after(after(tau)), first = tau }, none) @ after tau,
    }
    query fourFusion reserved(Slot { first = tau, second = after(after(tau)) }, none) @ after tau
}
```

| Construcción | Significado |
|---|---|
| `entity Thing` | Tipo de entidad |
| `entity Person { assets : Set Thing }` | Entidad con campos; `Set T` es un conjunto |
| `entity Buyer <: Person` | Subtipo: un `Buyer` vale donde se espera un `Person` |
| `const ana : Buyer` | Constante de un tipo |
| `const tau : PropositionTime` | Constante temporal |
| `Thing?` y `none` | Tipo opcional y su valor vacío |
| `Slot { first = tau, second = after(tau) }` | Valor record; el orden de los campos no importa |
| `after(tau)` | Como valor de un argumento, el instante siguiente; se anida: `after(after(tau))` |

## Verbos y eventos

```res
module Verbs

entity Thing
entity Person {
    assets : Set Thing
}

const juan : Person
const pedro : Person
const car : Thing
const tau : PropositionTime

seeded verb sells(subject : Person, object : Thing, recipient : Person)
derived verb owns(owner : Person, object : Thing)
effect verb give(subject : Person, object : Thing, recipient : Person) =>
    subject.assets -= object
    recipient.assets += object

rule sale(seller, object, buyer, t) =
    sells(seller, object, buyer) @ t <= give(seller, object, buyer) @ after t

experiment sold {
    seeds { sells(juan, car, pedro) @ tau, }
    state @ tau { juan.assets = {car}, pedro.assets = {}, }
    query residual give(juan, car, pedro) @ after tau
}
```

| Construcción | Significado |
|---|---|
| `seeded verb …` | Hecho de entrada; aparece en `seeds` |
| `derived verb …` | Conclusión de reglas |
| `effect verb … =>` con líneas `campo += valor` / `campo -= valor` | Cambia el estado al ejecutarse con `execute` |
| `verbo(args) @ t` | Un evento en un instante; tras `@` va un nombre (`@ tau`, `@ t`) o `after` y un nombre (`@ after t`), sin anidar |
| `~verbo(args) @ t` | Negación evidencial: evidencia de que es falso, no ausencia de prueba |

Con `./residuum execute`, `sold` termina con `juan.assets = {}` y
`pedro.assets = {car}`. Los efectos se aplican en orden de `after` sobre el
instante del `state`; dos efectos del mismo instante que añaden y quitan el
mismo valor se informan como conflicto ([README](../README.md)).

Un verbo puede asociarse a un Program que se activa cuando ocurre el evento
(programas de verbo activos, [active-verb-programs.md](active-verb-programs.md)):

```res
module VerbProgram

entity Thing
const item : Thing
const tau : PropositionTime

seeded verb starts(object : Thing) = program Finish
derived verb done(object : Thing)

rule finish(object, t) = I <= done(object) @ after t

program Finish(object : Thing, t : PropositionTime) {
    use finish { object = object, t = t }
}

experiment started {
    seeds { starts(item) @ tau, }
    query active residual done(item) @ after tau
}
```

## Reglas

```res
module Rules

entity Person
entity Thing

const ana : Person
const book : Thing
const oldDate : PropositionTime
const tau : PropositionTime

seeded verb requests(subject : Person, object : Thing)
seeded verb available(object : Thing)
seeded verb observed(subject : Person, effective : PropositionTime)
derived verb lent(subject : Person, object : Thing)
derived verb eligible(subject : Person, object : Thing)
derived verb recorded(subject : Person, effective : PropositionTime)
derived verb open(object : Thing)

// Horn: A <= C se lee "A implica C"; & une condiciones.
rule lending(person, object, t) =
    requests(person, object) @ t & available(object) @ t <= lent(person, object) @ t

// I es la condición vacía: la conclusión vale sin requisitos.
rule alwaysOpen(object, t) = I <= open(object) @ t

// Residual: dado requests, todavía falta available para concluir eligible.
rule eligibility(person, object, t) =
    requests(person, object) @ t
    <= available(object) @ t
    -o eligible(person, object) @ after t

// Aplicación parcial: los argumentos fijan los parámetros por orden.
rule remember(effective, t, subject) =
    observed(subject, effective) @ t <= recorded(subject, effective) @ after t
rule rememberOld = remember(oldDate)
rule rememberOldForAna = rememberOld(tau, ana)

experiment anaBorrows {
    seeds { requests(ana, book) @ tau, available(book) @ tau, }
    query residual lent(ana, book) @ tau
}
```

Las reglas son monotónicas: añadir hechos nunca retira una conclusión. Los
parámetros se declaran en la cabecera y sus tipos se infieren de los verbos.

## Programs

```res
module Programs

entity Person
const ana : Person
const bob : Person
const tau : PropositionTime

derived verb notified(person : Person)
derived verb served(person : Person)
derived verb linked(a : Person, b : Person)

rule service(person, t) = served(person) @ t <= notified(person) @ t
rule link(a, b, t) = linked(a, b) @ t <= served(b) @ t

// Cada `use` compila a su propia instancia de la regla.
program Both(a : Person, b : Person, t : PropositionTime) {
    use service { person = a, t = t }
    use service { person = b, t = t }
    use link { a = a, b = b, t = t }
}

// Aplicación parcial de un Program: fija `a`.
program ForAna = Both(ana)

experiment chain {
    premises { ~notified(bob) @ tau, }
    query fourFusion ~linked(ana, bob) @ tau
    using program Both
    with { program Both.a = ana, program Both.b = bob, program Both.t = tau }
}
```

Un Program agrupa reglas con parámetros compartidos. Se usa como ámbito de una
consulta (abajo) o se asocia a un verbo. Más detalle en
[minimal-programs.md](minimal-programs.md).

## Defaults

```res
module Defaults

entity Fact
entity Package
const Plain : Package
const Retention : Package
const saleCase : Fact
const tau : PropositionTime

seeded verb sale(id : Fact)
seeded verb retentionAgreed(sale : Fact)
derived verb selected(sale : Fact, package : Package)

rule normalSale(saleId, t) = sale(saleId) @ t <= selected(saleId, Plain) @ t
rule retentionSale(saleId, t) = sale(saleId) @ t <= selected(saleId, Retention) @ t

default NormalSale =
    supernormal normalSale
    blocked when
        retentionAgreed(saleId) @ t

default RetentionSale =
    exception retentionSale
    to NormalSale
    when
        retentionAgreed(saleId) @ t

experiment retention {
    seeds { sale(saleCase) @ tau, retentionAgreed(saleCase) @ tau, }
    query residual selected(saleCase, Retention) @ tau
}
```

| Construcción | Significado |
|---|---|
| `supernormal r` | La regla `r` se aplica por defecto |
| `blocked when C` | …salvo que se cumpla `C` |
| `exception r to D when C` | `r` derrota al default `D` cuando se cumple `C` |

Con `./residuum run`, `retention` bloquea `NormalSale` (hay
`retentionAgreed(saleCase)`) y selecciona `RetentionSale`. Las condiciones usan
los parámetros de la regla. `run` y `explain` evalúan los
defaults; las consultas residuales y FOUR rechazan módulos con defaults.
Diseño y pruebas en [program-defaults.md](program-defaults.md).

## Experimentos

Un experimento declara un escenario en el propio fichero:

| Parte | Forma |
|---|---|
| Entrada | `seeds { … }` (hechos de entrada) o `premises { … }` (hipótesis lógicas; exigidas por `fourFusion`) |
| Estado inicial | `state @ t { x.campo = {…}, … }`, sólo para `execute` |
| Consulta | Una de las de la sección siguiente |

## Consultas

| Consulta | Qué responde |
|---|---|
| `query residual G @ t` | Qué falta para el objetivo y explicaciones certificadas |
| `query residual G @ t using rules { r1, r2 } with { rule r1.x = c }` | Lo mismo, limitado a esas reglas con esos bindings |
| `… using program P with { program P.x = c }` | Lo mismo, con un Program como ámbito |
| `query active residual G @ t` | Lo mismo, activando los Programs asociados a verbos |
| `query fourFusion G @ t` | Si `G` se sigue en la lógica de cuatro valores (T, F, B, N), que capta la contraposición que Horn no deriva |
| `query fourFusion G @ t using … with { … }` | Lo mismo con reglas parametrizadas; todo parámetro que use un cuerpo del ámbito necesita binding |

```res
module Queries

entity Person
const alice : Person
const tau : PropositionTime

derived verb Notified(person : Person)
derived verb Served(person : Person)

rule service(person, t) = Served(person) @ t <= Notified(person) @ t

experiment contraposition {
    premises { ~Notified(alice) @ tau, }
    query fourFusion ~Served(alice) @ tau
    using rules { service }
    with { rule service.person = alice, rule service.t = tau }
}
```

`./residuum query` da `Horn: false` y
`FOUR least model: true (goal T; 2 atoms, 3 clauses; explicit scope)`. Con un
ámbito, un `true` vale para todo el módulo; un `false` sólo dice que esas
instancias no bastan. `with` exige `using`; `fourFusion` no admite `active`.
Detalle en [executable-fixtures.md](executable-fixtures.md) y
[residual-query-source-bindings.md](residual-query-source-bindings.md).

## Sólo desde Rust

Estas capacidades no tienen sintaxis `.res` ni orden de CLI:

- Costes de prueba: `derive::minimum_proof_sizes` (derivación mínima por
  conclusión) y `derive::kleene_stages` (profundidad); véase
  [semi-naive-pending-optimizations.md](semi-naive-pending-optimizations.md) §9.
- Evaluadores incrementales y por pasos: `IncrementalClosure`,
  `IncrementalProgramClosure`, `DerivativeSession`, `ForwardSession`.
- El evaluador FOUR directo: `experiments::GroundProgram`,
  `experiments::four_least_model`, `experiments::FourSession`.
- El frontend CNL pausado: `parse_cnl`, `elaborate_cnl`.
