# Programas experimentales con datos y consultas

Los experimentos ahora se definen en archivos Formal. Rust los parsea, elabora
y ejecuta; los tests comprueban resultados sin fabricar sus eventos de entrada.
`examples/run_fixture.rs` acepta un archivo de experimento, sin construir una CLI
general. En modo incremental puede recibir una biblioteca de declaraciones con
`--library`, para el [experimento de reutilización](owns-reuse-experiment.md).

```text
archivo .res → parser → SurfaceAST → TypedAST → consulta/cierre → salida
```

## ResidualProof

[residual_proof.res](../examples/experiments/residual_proof.res) contiene entidades,
constantes, verbos seeded, el cuerpo real de `give`, `sales` y tres escenarios.

```text
experiment empty {
    seeds {}
    query residual give(alice, car, bob) @ after tau
}
```

`priceOnly` y `both` escriben sus eventos dentro de `seeds {...}`. Cada escenario
tiene entrada independiente. Las comas internas son obligatorias; sólo la final
es opcional. `seeds {}` es conocimiento vacío, no `I`.

```sh
python3 scripts/test_safe.py --fixture examples/experiments/residual_proof.res
```

Con A como acuerdo de precio y B como acuerdo de objeto, la salida observada es:

| Experimento | Seeds | Requisito | Horn deriva give |
| --- | --- | --- | --- |
| `empty` | `∅` | `A ⊗ B` | No |
| `priceOnly` | `{A}` | `B` | No |
| `both` | `{A,B}` | `I` | Sí |

La consulta utiliza las seeds originales y se calcula un cierre separado para
mostrar qué se deriva. No se afirman requisitos, no se mezclan los escenarios
y no se ejecutan efectos ni se modifican snapshots.

Los argumentos deben ser constantes declaradas con tipos compatibles. El
índice se declara con `const tau : PropositionTime`. Tiempo sin declarar,
argumentos desconocidos, aridad incorrecta o tipos incompatibles fallan durante
elaboración. Las entradas `seeds` admiten exclusivamente verbos Seeded.

## Comparación FOUR desde el propio programa

[four_counterexample.res](../examples/experiments/four_counterexample.res) escribe
P, Q, la regla y la teoría consultada:

```text
const tau : PropositionTime
derived verb P()
derived verb Q()

rule implication() = P() @ tau <= Q() @ tau

experiment contraposition {
    premises { ~Q() @ tau, }
    query fourFusion ~P() @ tau
}
```

La constante temporal no se infiere como parámetro de esa regla. `premises`
identifica hipótesis lógicas de una comparación; no afirma que una proposición
Derived haya sido derivada externamente. El runner mantiene esa distinción:
por ahora residual requiere `seeds` y fourFusion requiere `premises`.

```sh
python3 scripts/test_safe.py --fixture examples/experiments/four_counterexample.res
```

Salida observada:

```text
experiment contraposition
  Premises: {~Q() @ tau}
  goal: ~P() @ tau
  Horn: false
  Known after close: {~Q() @ tau}
  FOUR fusion: true (3 models / 16 interpretations)
  FOUR least model: true (goal T; 2 atoms, 3 clauses)
```

Usa fusión FOUR, filtro de I y reglas como desigualdades de verdad, según el
[experimento semántico](four-model-entailment.md). Decide el modelo
\(\le_k\)-mínimo ([§12](semi-naive-pending-optimizations.md)): la línea
`FOUR least model` da la consecuencia, el valor del objetivo en FOUR
(T, F, B o N) y el tamaño del programa compilado. Con hasta cuatro átomos se
enumeran además todas las interpretaciones; la línea `FOUR fusion` es esa
comprobación de referencia y coincide siempre en la consecuencia. Con más
átomos solo aparece el modelo mínimo. No incorpora la conclusión algebraica a
`Known` ni introduce contraposition en `close`.

## FOUR con ámbito y bindings explícitos

[four_scoped_bindings.res](../examples/experiments/four_scoped_bindings.res)
usa la misma sintaxis `using`/`with` que las consultas residuales para
instanciar reglas con parámetros:

```text
rule service(person, t) =
    Served(person) @ t <= Notified(person) @ t

experiment contraposition {
    premises { ~Notified(alice) @ tau, }
    query fourFusion ~Served(alice) @ tau
    using rules { service }
    with { rule service.person = alice, rule service.t = tau }
}
```

La selección del ámbito y la validación de los bindings son las de las
consultas residuales (`resolve_scoped_bindings`). Después, cada regla del
ámbito se instancia con sus bindings (`GroundProgram::for_experiment`, la única
entrada para consultas con o sin opciones). Todo parámetro que aparece en el
cuerpo de una regla del ámbito necesita un binding; si falta, la elaboración
falla con un error que nombra el destino `with` que lo fijaría
(`rule service.t`, `program Service.person`). Un parámetro compartido de un
Program que una de sus reglas no menciona no necesita binding en ella. No se
buscan valores entre las constantes del módulo. No se aplica el preflight
residual sobre el objetivo, porque un modelo FOUR restringe todas las
instancias del ámbito y no solo las que producen el objetivo; la
contraposición recorre las reglas hacia atrás.

Con ámbito, los bindings definen la teoría. Por eso la línea `Horn` y
`Known after close` usan las mismas instancias que FOUR, y el informe muestra
`search scope` y `query bindings`, como en las consultas residuales.

El resultado se marca `explicit scope`. Cada regla restringe los modelos, de
modo que una consecuencia en el ámbito también lo es del módulo completo: los
modelos del módulo, restringidos a los átomos del ámbito, son modelos del
ámbito. El test `adding_rules_never_withdraws_an_entailment` comprueba esa
monotonía sobre conjuntos de reglas ground, que es lo que produce la
instanciación. Un `false` solo dice que estas instancias no bastan:
`otherInstance` instancia la regla para `bob` y no concluye nada sobre
`alice`.

Cada regla o RuleUse aporta una sola instancia: los bindings duplicados se
rechazan, así que `service` para `alice` y para `bob` no caben en el mismo
ámbito, y `rule r.x = c` fija el mismo valor en todos los usos de `r` dentro de
un Program. `active` sigue sin admitirse con `fourFusion`. `steps` recorre la
enumeración de las mismas instancias, hasta cuatro átomos, y termina con la
misma línea `FOUR least model` que `query`.

## Alcance y ejecución segura

`fourFusion` nombra explícitamente el modelo de la consulta, sin adoptarlo como
semántica operacional general de M2. Exige argumentos constantes y un único
tiempo común; sin ámbito explícito, además, reglas sin parámetros. La
enumeración y `steps` siguen limitadas a cuatro átomos ground; el modelo
mínimo no tiene ese límite. Esta
última restricción evita confundir el matching actual de nombres temporales
con un nuevo chequeo de constantes literales entre índices distintos. El matcher
no se cambia en este incremento.

El modo residual exige dependencias acíclicas entre verbos, una condición
suficiente de terminación para estas fixtures. FOUR admite ciclos ground dentro
de su universo finito. Se rechazan defaults. Estos modos no añaden `!`, derivada discreta,
preferencia abductiva, ejecución de snapshots ni drafter. CNL permanece pausado.

El archivo raíz sigue siendo regular y de hasta 64 KiB por el control separado
de `test_safe.py --fixture`. El resolver admite hasta 1 MiB sumando todos los
archivos únicos del grafo de imports, incluidos raíz y comentarios, y conserva
`MAX_MODULES = 64`. La cota de fuente es configuración de implementación; el tag
`v1` permanece en 64 KiB. `test_safe.py --fixture` compila el ejemplo y lo ejecuta
en fases y cgroups separados: 1 GiB total, sin swap, un
trabajo de Cargo, timeout de compilación de 45 s y ejecución de 15 s. Conserva la
detención por crecimiento anormal y cercanía al límite. `--fixture` no se combina
con opciones de tests ni dispara la suite completa.

Se verificaron seis tests nuevos y tres regresiones individualmente. Ambos
programas también se ejecutaron desde sus archivos. El pico RSS fue 638 MiB al
compilar tests y aproximadamente 15 MiB al ejecutar las fixtures.

El modo externo `--incremental`, documentado en
[incremental-close.md](incremental-close.md), compara la actualización forward
con una recomputación completa sobre los bloques `base` y `delta`. Reutiliza
la gramática de experimentos y no ejecuta sus consultas residuales.
