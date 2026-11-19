# Optimizaciones pendientes del cierre semi-naive

Inventario de 2026-10-29 (punto 12 añadido el 2026-11-01 e implementado el 2026-11-18), posterior a la rama `semi-naive-dedup-index`
(índice en `IncrementalClosure`, deduplicación con `BTreeSet`, pivotes sin
repetición y `new_by_derivative`). Ordena trabajo posible. El impacto de cada
entrada es una estimación por lectura del código, salvo en las marcadas como
aplicadas (§1, §2, §5 en parte, §9 y §12, 2026-11-18), que describen el cambio
hecho, cómo se verificó y lo que se midió. Las demás siguen sin implementar.

Cada entrada separa el problema observado, la propuesta, lo que debe
conservarse y cómo verificarla. Salvo que se diga lo contrario, todas deben
preservar los eventos lógicos, el conjunto de justificaciones, su multiplicidad
de un sello por justificación y la independencia de `DerivationTime` respecto
de rondas y `PropositionTime` ([discrete-derivative.md](discrete-derivative.md) §§3, 6).

## Resumen

| # | Optimización | Impacto estimado | Riesgo | Toca |
|---:|---|---|---|---|
| 1 | Índice por argumentos ya ligados | Alto | Medio | `known_index.rs`, matching — **aplicada** |
| 2 | Mapa verbo → reglas relevantes | Medio | Bajo | `incremental.rs`, `program_incremental.rs` — **aplicada** |
| 3 | Orden de uniones por selectividad | Medio | Medio | `match_delta_antecedents` |
| 4 | Evaluación por componentes de dependencia | Medio | Medio | schedulers de cierre |
| 5 | Menos copias en el join | Medio (constante) | Bajo | matching — **aplicada** en parte |
| 6 | Rondas con instantánea de Known | Bajo–medio | Medio | `update`, `drain` |
| 7 | Explicación bajo demanda | Alto en memoria | Alto (contrato) | `Closure`, `explain` |
| 8 | Procedencia en semianillos | Nueva capacidad | Alto (diseño) | capa de consulta |
| 9 | Prueba mínima: tropical y (min, max) | Nueva capacidad; `explain` más legible | Medio | capa de procedencia, `explain` — **aplicada** como pasada posterior |
| 10 | Uniones *worst-case optimal* | Alto en cuerpos cíclicos | Alto | matching |
| 11 | Evaluación dirigida por objetivo | Depende de la consulta | Alto | residual / forward |
| 12 | FOUR por modelo menos informado | Alto: de 4ⁿ a polinomial | Medio | `experiments/four.rs` — **aplicada** e integrada en `run_experiments` (2026-11-19) |

Fuera de alcance por diseño: `close` sigue siendo el cierre ingenuo de
referencia y oráculo de comparación. Las optimizaciones van en los evaluadores
incrementales; `new_by_derivative` ya ofrece una base construida por derivada.

## 1. Índice por argumentos ya ligados

**Problema.** `KnownIndex` agrupa sólo por verbo, polaridad y aridad. En
`present(x) & motive(x)`, con `x` ya ligado por el pivote, el join recorre
todos los `motive(...)` y llama a `match_event` con cada uno.

**Propuesta.** Índice secundario por posición de argumento y término ground,
consultado cuando el patrón tiene esa posición ya ligada en los bindings
actuales. Puede construirse de forma perezosa por (verbo, posición) la primera
vez que un patrón lo requiera.

**Conservar.** `Candidates` debe seguir devolviendo eventos en el orden de
Known para que el orden de descubrimiento, y por tanto la asignación de sellos,
no cambie. Los términos no ground (`RecordLiteral` con variables, constructores
temporales) siguen por el camino actual.

**Verificar.** Comparar indexado contra `profile::linear_scan()` como en
`indexed_known_matches_linear_product_with_identical_provenance`: misma
igualdad `Debug` de cierres y mismos conteos salvo `probes` y `header_rejects`.

**Aplicado (2026-11-18).** `KnownIndex::with_arguments` añade a cada cubeta
de encabezado un mapa por posición de argumento, de término ground exacto a
posiciones ascendentes en Known; se construye de forma ansiosa, no perezosa.
Lo usan los Known de nivel de cierre (`close`, `IncrementalClosure`,
`IncrementalProgramClosure`, `ForwardSession`); las fronteras siguen con el
índice de encabezado. `ForwardSession` conserva su índice entre pasos y lo
extiende con los eventos añadidos, en lugar de reconstruirlo en cada paso. `KnownView::candidates_bound` elige, entre las
posiciones fijadas, la de menos posiciones: una constante o `None`, o un
parámetro de tipo no temporal ya ligado a un término ground. Para esos casos
`bind_term` sólo acepta igualdad exacta, así que el filtro no pierde ningún
candidato y conserva el orden de Known. Los parámetros de tipo
`PropositionTime`, los constructores y los records siguen el camino de
encabezado, porque su comparación canónica no es igualdad sintáctica.

Verificación: `argument_index_matches_linear_product_with_identical_provenance`
(`Debug` idéntico al barrido lineal en `partialProduct`, mismos contadores
salvo sondeos, y cada sondeo ahorrado era un rechazo estructural) y
`argument_index_keeps_incremental_updates_equal_to_linear_scan`. El test
anterior del índice de encabezado se conserva con `profile::header_only_index`.
`src/derive/known_index_tests.rs` añade dos comparaciones. Una aleatoria, con
semilla fija: `candidates_bound` contiene, en orden de Known, todo evento que
`match_event` acepta, con constantes, `None`, records, constructores,
parámetros de entidad, opcionales y temporales, variables que no son
parámetros, ligaduras no ground o mal tipadas y eventos no ground en Known. Y
un barrido de todas las fixtures de `examples/`: 122 módulos y 280
experimentos, con `close` e `IncrementalClosure` (o `IncrementalProgramClosure`
si el módulo tiene Programs, con activaciones) y `ForwardSession`, dan el mismo
`Debug` que el barrido lineal. Quedan fuera, por el tiempo límite del runner
con el barrido lineal, seis fixtures de carga: `peano_after`,
`peano_multiplication`, `peano_polynomial_scenario`,
`peano_polynomial_product_scenario` (su `partialProduct` se compara arriba),
`program_incremental_scaling` y `program_proof_scaling`.
Observado una vez, build de tests sin optimizar: sondeos 93 306 → 22 293,
rechazos estructurales 81 277 → 10 264, `matching_ms` 632 → 248.

## 2. Mapa verbo → reglas relevantes

**Problema.** Cada ronda de `update` examina todas las reglas
(`rules_examined`), aunque ningún evento de la frontera tenga un verbo que
aparezca en sus antecedentes.

**Propuesta.** Precalcular, al construir el estado, el conjunto de reglas por
(verbo, polaridad) de sus átomos. Por ronda, examinar sólo la unión de las
reglas asociadas a los encabezados de la frontera. Igual para las reglas de
activaciones en `IncrementalProgramClosure`.

**Conservar.** El orden relativo de las reglas examinadas debe ser el orden de
`rules`, para no alterar el orden de descubrimiento. `rules_examined` bajará;
los tests que fijan `rules_examined == 0` en actualizaciones duplicadas siguen
valiendo.

**Verificar.** Los tests existentes de igualdad con `close` y un test que
compare la secuencia de `delta.derivations` con y sin el filtro.

**Aplicado (2026-11-18).** `derive/relevance.rs` precalcula, por regla, los
encabezados (verbo, polaridad, aridad) de sus átomos. En cada ronda delta,
`IncrementalClosure::update` y `IncrementalProgramClosure` (reglas ordinarias
y reglas de programas activados) examinan sólo las reglas con algún encabezado
presente en la frontera, en el orden de `rules`. Es exacto porque
`match_event` rechaza todo par con verbo, polaridad o aridad distintos, así que
una regla sin encabezados en la frontera no tiene pivote. Las inicializaciones
completas (ronda inicial y activaciones nuevas) no se filtran. Las reglas con
sólo `I` nunca tenían match delta y ahora no se examinan.

Verificación: `relevant_rules_keep_every_incremental_delta_and_its_order` y
`relevant_rules_keep_program_closure_deltas_and_activations` comparan, con y
sin el filtro (`profile::every_rule`), cierres, `delta.known`,
`delta.derivations`, activaciones, inicializaciones, rondas, pivotes y matches
completos en actualizaciones de una semilla sobre los escenarios del producto.
`rules_examined` pasó de 2 544 a 72 (reglas ordinarias) y de 18 221 a 3 696
(cierre con programas).
`src/derive/relevance_tests.rs` extiende la comparación a todas las fixtures
de `examples/` salvo seis de carga (las mismas que `known_index_tests.rs`):
243 experimentos comparados, con `IncrementalClosure` o
`IncrementalProgramClosure` según el módulo, en un lote de varios eventos y
evento por evento; otros 38, de módulos con Programs cuyo cierre no se puede
construir (`IncrementalProgramClosure::new` falla), no se cuentan. El filtro se
saltó unos 33 000 exámenes de regla sin cambiar ningún delta ni cierre. En 4
experimentos se saltó trabajo en módulos con reglas residuales, en 58 en
módulos con reglas de sólo `I` y en 125 en módulos con átomos
`EvidentialNot`; eso muestra que esos módulos están cubiertos, no que se haya
saltado precisamente una regla de cada tipo.

Cambio observable: `IncrementalStats.rules_examined`, que imprime la salida
`--incremental`, cuenta ahora sólo las reglas relevantes a la frontera de cada
ronda, así que depende de los encabezados de la frontera además del número de
reglas y rondas. `sells_tests` compara las estadísticas de dos actualizaciones
equivalentes; sigue valiendo porque sus fronteras tienen los mismos
encabezados en cada ronda.

## 3. Orden de uniones por selectividad

**Problema.** Tras el pivote, los demás conjuntos se unen en el orden escrito
en la regla. Un átomo muy selectivo al final multiplica resultados intermedios.

**Propuesta.** Elegir el orden de los no-pivotes según el tamaño de su bucket
en el índice (o según argumentos ya ligados, si existe el índice del punto 1).

**Conservar.** El vector de testigos ya se reconstruye en el orden original;
eso debe mantenerse. El orden de los matches devueltos puede cambiar, así que
el resultado debe reordenarse a un orden canónico antes de retenerse, o este
cambio debe aceptar explícitamente otra asignación de sellos.

**Verificar.** Igualdad de conjuntos de justificaciones contra `close`; si se
reordena canónicamente, igualdad exacta de secuencias.

## 4. Evaluación por componentes de dependencia

**Problema.** Todas las reglas participan en cada ronda hasta el punto fijo
global, aunque partes no recursivas del programa ya se hayan estabilizado.

**Propuesta.** Grafo de dependencias verbo de antecedente → verbo de
consecuente; evaluar sus componentes fuertemente conexas en orden topológico,
cada una hasta su punto fijo. Con activaciones de `Verb.program`, el grafo
crece en tiempo de ejecución; el orden debe recalcularse o limitarse a las
reglas ordinarias.

**Conservar.** El conjunto de eventos y justificaciones es el mismo menor
punto fijo (§3 admite schedules distintos). El orden de descubrimiento sí
cambia: decidir si se acepta o si se documenta como modo separado.

**Verificar.** Comparación por conjuntos contra `close`, incluidos programas
con ciclos (`program_incremental_cycles.res`).

## 5. Menos copias en el join

**Problema.** Por cada candidato se clonan `bindings` (`BTreeMap`) y el vector
de testigos, y los testigos son `Event` completos.

**Propuesta.** Testigos como posiciones en Known (`usize`) durante el join,
convertidos a `Event` sólo al construir el `AntecedentMatch` final; bindings
como pila con deshacer en vez de mapas clonados. A más largo plazo, internar
eventos con identificadores estables.

**Conservar.** `AntecedentMatch` y `DerivationRecord` no cambian de forma.

**Verificar.** Mismos resultados exactos; medir con el profiler
`profile_semi_naive_polynomial_product_fixture`.

**Aplicado en parte (2026-11-18).** `derive/join.rs` sustituye los joins en
anchura de `match_antecedents_in` y `match_delta_antecedents` por una búsqueda
en profundidad con un solo mapa de bindings y testigos como referencias a
Known, clonados sólo al completar un match. Un intento de `match_event` se
deshace quitando los binders que no estaban. Basta porque `bind_typed` sólo
inserta valores canónicos y, ante un binder presente, reescribe la forma
canónica de un valor igual: para los valores puestos durante el join es el
mismo valor. Un valor inicial puede no serlo (las ligaduras de activación se
canonizan con los tipos de parámetro de la fuente del Program, no de la
regla); entonces sólo un binder `PropositionTime` puede cambiar de
representación, de término a tiempo igual, y ese cambio sobrevive al deshacer.
No es observable: todo match completo liga todos los binders, así que la
salida lleva la forma canónica de todos modos, y el índice de argumentos sólo
lee parámetros no temporales, cuya forma canónica es el propio valor. Recorrer los átomos en orden y los candidatos en orden de Known da los
matches en el mismo orden lexicográfico que el join en anchura. Los joins
anteriores quedan como referencia de test (`profile::reference_join`).

No se hizo: testigos como posiciones `usize`, bindings como pila sin mapa ni
eventos internados.

Verificación: `depth_first_join_matches_copying_join_with_identical_provenance`
(`Debug` idéntico en `partialProduct` y los mismos contadores, incluidos
sondeos y rechazos) y `depth_first_delta_join_keeps_incremental_updates`
(deltas y cierres de `IncrementalClosure` e `IncrementalProgramClosure` en tres
escenarios, una semilla por actualización);
`depth_first_delta_join_keeps_batch_updates_and_temporal_boundaries` (lotes de
varios eventos, de modo que un match tenga varios testigos en la frontera y se
use la exclusión antes del pivote, en cuatro fixtures base/delta, incluida
`dynamic_incremental_temporal_boundary.res`, y en los productos en uno y dos
lotes); y el barrido de todas las fixtures de `known_index_tests.rs`, que
compara también con el join de referencia. Además, 89 tests existentes de incremental, residual, regresión
monótona y Peano, ejecutados individualmente. `matching_ms` en `partialProduct`,
build de tests sin optimizar, dos corridas: 566 → 382 y 596 → 486.

## 6. Rondas con instantánea de Known

**Problema.** Known crece a mitad de ronda (estilo Gauss-Seidel). Un match
puede descubrirse en una ronda y otra vez en la siguiente; el `BTreeSet` lo
descarta, pero el trabajo de encontrarlo ya se hizo. Tras `semi-naive-dedup-index`
no quedan repeticiones dentro de una misma llamada, sólo entre rondas.

**Propuesta.** Cada ronda lee Known hasta la longitud que tenía al comenzar;
los eventos de la ronda actual se usan desde la siguiente. Con las posiciones
anteriores al pivote fuera de la frontera y las posteriores dentro de la
instantánea, cada match se produce exactamente una vez en toda la evaluación.

**Conservar.** El menor punto fijo. Puede aumentar el número de rondas y
cambiar el orden de descubrimiento y de sellos.

**Verificar.** Que `full_matches` sea igual al número de justificaciones
retenidas en las fixtures forward, además de la igualdad con `close`.

## 7. Explicación bajo demanda

**Observación matemática.** Por la definición del §6, las justificaciones son
función del cierre: \(J_R(X)\) es el conjunto de instancias con todos sus
testigos en X. Guardarlas durante el cierre forward es un caché, no una
necesidad lógica. Para el goal de un escenario basta recorrer hacia atrás su
cono: instancias cuya conclusión es el evento y cuyos testigos están en el
cierre, recursivamente. El costo es proporcional a la explicación, no al
cierre completo. ΔJ es la misma derivada aplicada a J.

**Pendiente de investigar.**

- `derivedAt` proviene del reloj externo y no se puede recalcular desde el
  cierre. Si `explain` lo necesita, debe guardarse o sustituirse por un dato
  canónico, como la etapa de Kleene: la menor ronda n con el evento en Tⁿ.
- Si `explain` debe mostrar todas las justificaciones del expediente o sólo las
  del cono del goal.
- Defaults, cláusulas residuales y activaciones de programas: su evaluación no
  es Horn positivo puro y requiere conservar estado de selección y activación.

**Conservar.** El contrato actual de `ClosureDelta.derivations`. Un modo bajo
demanda sería una API nueva, no un reemplazo.

## 8. Procedencia en semianillos

**Observación.** Green, Karvounarakis y Tannen (2007) unifican las formas de
procedencia como evaluación de la misma expresión en distintos semianillos.
Para Residuum:

| Semianillo | Pregunta |
|---|---|
| Booleano (∨, ∧) | ¿se deriva? (el cierre actual) |
| Conjuntos de soportes | ¿qué seeds bastan? (*why-provenance*) |
| Tropical (min, +) | prueba más pequeña o más barata |
| (min, max) | profundidad mínima: la etapa de Kleene |
| Conteo (+, ×) | cuántas derivaciones hay |

Como el cierre es monótono, la familia de conjuntos de seeds que derivan un
goal es ascendente en \(\mathcal P(\text{Seeds})\). Queda determinada por su
anticadena de soportes mínimos: es la misma estructura que usa el experimento
de [recalcitrancia](legal-recalcitrance-justificatory-functions.md)
con anticadenas de soportes. Esa anticadena puede mantenerse
con la derivada aditiva.

Con suma idempotente (booleano, soportes, tropical, (min, max)) la evaluación semi-naive
sigue siendo válida; el conteo requiere otro tratamiento porque su suma no es
idempotente. Khamis, Ngo, Pichler, Suciu y Wang (PODS 2022) estudian la
convergencia de Datalog sobre semianillos. El tropical se desarrolla en el
punto 9.

**Pendiente de investigar.** Interpretación de `EvidentialNot`, del axioma
`I <= C` (unidad del semianillo) y de la fusión FOUR en este marco.

## 9. Prueba mínima: semianillo tropical y (min, max)

**Idea.** En el semianillo tropical (min, +), el «y» de un cuerpo suma costos
y el «o» entre justificaciones alternativas toma el mínimo. Asignando un costo
a cada regla (y a cada seed, 0 por defecto), cada evento recibe

\[
c(e)=\min_{j\in J,\;head(j)=e}\Bigl(w(rule(j))+\sum_{a\in witnesses(j)}c(a)\Bigr).
\]

Con costo 1 por regla, \(c(e)\) es el **tamaño** del menor árbol de prueba
(subpruebas compartidas cuentan una vez por uso). Con pesos por tipo de regla o
de evidencia, es la explicación «más barata».

La **profundidad** no sale de (min, +), sino del semianillo (min, max): mínimo
entre justificaciones y máximo entre testigos,
\(d(e)=\min_j\bigl(1+\max_{a}d(a)\bigr)\), con \(d=0\) para seeds y \(d=1\)
para un axioma `I <= C`. Ése es exactamente la etapa de Kleene del punto 7, la
menor ronda n con el evento en Tⁿ, y es el dato reproducible que puede
sustituir a `derivedAt` en comparaciones. Ambos semianillos tienen suma
idempotente; todo lo que sigue vale para los dos.

**Usos.** `explain` puede presentar primero la prueba de costo mínimo, y las
demás justificaciones sólo a petición; los empates se conservan, no se
desempatan por orden de descubrimiento. Es independiente del reloj y del
schedule, así que sirve para comparar ejecuciones.

**Algoritmo.** Es un problema de caminos más cortos en el hipergrafo de
justificaciones (Datalog tropical ≈ Bellman-Ford). Con pesos no negativos,
la generalización de Dijkstra de Knuth (1977) para hipergrafos fija cada evento
una sola vez en orden de costo creciente. La suma min es idempotente, así que
la evaluación semi-naive sigue siendo válida, y la convergencia está asegurada
con pesos no negativos aunque haya ciclos.

**Consecuencia para la derivada.** En el cierre booleano, un evento ya conocido
no vuelve a la frontera. En el tropical, una adición puede **mejorar** el costo
de un evento viejo al abrir una prueba más corta. La acción de cambio pasa a
ser \(c\mapsto\min(c,\Delta c)\), monótona en el orden invertido de costos,
y la frontera debe incluir los eventos cuyo costo bajó, no sólo los nuevos.
Ésa es la diferencia de diseño respecto de los evaluadores incrementales,
que hoy registran una prueba nueva de un evento viejo sin volver a programarlo
(comentario en `program_incremental.rs`, `retain`; mismo comportamiento en
`IncrementalClosure::update`).

**Conservar.** El cierre de eventos y el conjunto de justificaciones no
cambian; el costo es una anotación adicional calculada sobre ellos. Puede
calcularse en una pasada posterior sobre las justificaciones ya retenidas, sin
tocar el cierre forward, como primer paso de bajo riesgo.

**Verificar.** Comparar contra la enumeración exhaustiva de pruebas en las
fixtures pequeñas (`forward_provenance.res` tiene dos caminos a `shared`) y
contra un Bellman-Ford de referencia sobre el hipergrafo.

**Aplicado como pasada posterior (2026-11-18).** `derive::minimum_proof_sizes`
(tropical, con un peso por justificación) y `derive::kleene_stages`
((min, max)) anotan un `Closure` ya calculado sin modificarlo; las semillas se
pasan explícitamente porque el cierre no las marca. El algoritmo es la
generalización de Dijkstra de Knuth: cada evento se fija una vez en orden de
costo creciente, también con ciclos. `ProofCosts.optimal` conserva las
justificaciones que alcanzan el mínimo y cuyos testigos se fijaron antes que el
evento, en el orden de `closure.derivations`; seguir cualquiera de ellas termina
siempre en semillas, y todo evento con costo tiene al menos una. Si cada
testigo cuesta estrictamente menos que la cabeza (pesos de al menos 1, sin
saturación) eso no excluye nada. Si un testigo puede costar lo mismo que la
cabeza (peso 0, o saturación) el conjunto informado es un subconjunto correcto
que depende del orden de fijación: descarta las que cerrarían un ciclo
(P ← Q ← P con costo 0) y puede descartar también alguna acíclica (Q ⇐ P si
los axiomas P y Q cuestan 0 y Q se fijó antes). Los tamaños
saturan en `u64::MAX`, que significa «al menos `u64::MAX`»: el tamaño de árbol
cuenta un subárbol compartido una vez por uso y puede crecer exponencialmente.

Verificación (`src/derive/proof_cost_tests.rs`): en `forward_provenance.res`
`shared` tiene costo 1 con las dos justificaciones `fromA` y `fromB`, `result`
2 y el axioma `ready` costo y etapa 1; tamaños con peso unitario y no uniforme
y etapas coinciden con una relajación tipo Bellman-Ford en cuatro escenarios
del producto y en los 2ⁿ subconjuntos de semillas de
`discrete_derivative.res` (con ciclos); y la etapa de cada evento es la ronda
en que `ForwardSession` lo añade. Con peso 0 los costos coinciden con la
referencia, las justificaciones informadas son un subconjunto de las que
alcanzan el mínimo y el grafo que forman no tiene ciclos; con peso `u64::MAX`
los tamaños saturan sin desbordar; los eventos sin prueba desde las semillas
dadas quedan en `None`, y una semilla que no está en Known no cambia nada.

Pendiente: presentarlo en `explain`, y la versión incremental, en la que una
adición puede bajar el costo de un evento viejo y la frontera debe incluirlo.

## 10. Uniones *worst-case optimal*

Para cuerpos con variables compartidas en ciclo (`e(x,y) & e(y,z) & e(z,x)`),
los joins binarios pueden producir intermedios mayores que el resultado.
Algoritmos como Leapfrog Triejoin o Generic Join tienen cota óptima en el peor
caso. Requieren índices ordenados por variable; dependen del punto 1. Sólo vale
la pena si aparecen reglas de ese tipo en las ontologías reales.

## 11. Evaluación dirigida por objetivo

El cierre forward calcula todas las consecuencias. Cuando sólo interesa un goal,
transformaciones como *magic sets* restringen la evaluación a lo relevante para
él. La búsqueda residual ya es backward; habría que delimitar qué fragmento del
forward se beneficia sin duplicar su contrato.

## 12. Consecuencia FOUR por modelo menos informado

**Problema.** `experiments/four.rs` decide `fourFusion` enumerando las
\(4^n\) interpretaciones de los átomos ground y conservando las que satisfacen
premisas y reglas. Por eso `prepare` limita el experimento a cuatro átomos.
`FourSession` refina por pasos eliminando mundos, pero recorre el mismo
universo.

**Observación.** Cada valor es un par de bits `Value { p, n }`. Con la
semántica de `four.rs`, todas las condiciones de modelo son cláusulas Horn
sobre las \(2n\) variables booleanas \(p_i, n_i\):

- Premisa `A`: \(p(A)\). Un literal negativo intercambia los componentes:
  `~A` aporta \(n(A)\).
- Regla `a <= c`, por `Value::le` (\((\lnot a.p\lor c.p)\land(\lnot c.n\lor a.n)\)):
  - **hacia adelante:** \(P(a)\Rightarrow c.p\), donde \(P(a)\) es el
    conjunto de componentes p de los literales de `a` (`I` no aporta ninguno,
    porque vale \((1,1)\));
  - **hacia atrás:** \(c.n\Rightarrow a.n\). Como
    \(n(x\otimes y)=(y.p\Rightarrow x.n)\land(x.p\Rightarrow y.n)\), se
    compila recursivamente con una guarda G, que empieza en \(\{c.n\}\):
    en un literal da \(G\Rightarrow\ell.n\); en \(x\otimes y\) baja a
    x con \(G\cup P(y)\) y a y con \(G\cup P(x)\); `I` no da nada.

Todas tienen exactamente una conclusión, así que el conjunto de modelos es
cerrado bajo la conjunción componente a componente, que es el meet del orden de
conocimiento \(\le_k\). El conjunto no es vacío (todo B es modelo), así que
existe el **modelo \(\le_k\)-mínimo**, y como \(p\) es monótono en
\(\le_k\):

\[
\text{entailed}(g)\iff p(g)\text{ en el modelo }\le_k\text{-mínimo.}
\]

**Propuesta.** Compilar las cláusulas anteriores y calcular el modelo mínimo
por propagación unitaria Horn, partiendo de todo U: es la iteración de Kleene de
un operador de consecuencias. El costo es lineal en el tamaño de las cláusulas
compiladas (cuadrático en el tamaño de cada cuerpo), en lugar de \(4^n\), y
permite levantar el límite de cuatro átomos.

**Diferencia con Fitting.** El operador de consecuencias de Fitting para
bilátices sólo propaga hacia adelante. Aquí el componente n también viaja de la
conclusión a las premisas, por la segunda mitad de `Value::le`. Copiar sólo la
dirección forward daría modelos que no satisfacen las reglas.

**Límites.** El argumento depende de que las conclusiones sean literales. Una
conclusión con disyunción rompería la forma Horn; en ese caso el problema es
difícil en general. El cierre Horn y esta consecuencia FOUR siguen siendo
objetos distintos ([discrete-derivative.md](discrete-derivative.md) §7): el
modelo mínimo vive en los pares (p, n), no en Known.

Como justificación teórica, la descomposición de FOUR en dos componentes es la
representación como producto que Cabrer y Priestley obtienen como consecuencia
de una dualidad natural por *piggyback* sobre Priestley. El algoritmo no la
necesita.

**Conservar.** `FourEntailment.entailed` debe coincidir. `models` e
`interpretations` cuentan mundos y no se obtienen del modelo mínimo; un
evaluador nuevo debería ofrecerlo como modo aparte, con la enumeración como
oráculo en el dominio pequeño.

**Verificado (experimento finito, no prueba formal).**
[scripts/four_least_model_check.py](../scripts/four_least_model_check.py)
copia `tensor` y `le` de `four.rs` y genera 5.000 programas ground al azar de
hasta tres átomos, con conjunciones anidadas, `I` y literales negativos. En
todos, el meet \(\le_k\) de los modelos es modelo, y la enumeración, el modelo
mínimo y la propagación compilada dan la misma consecuencia. No ejecuta código
Rust: falta un test que compare un evaluador Rust contra `entailment` en las
fixtures existentes.

**Aplicado (2026-11-18).** `experiments::four_least_model` compila las
cláusulas anteriores sobre los bits \((p_i, n_i)\) y calcula el modelo
\(\le_k\)-mínimo por propagación unitaria con contadores, lineal en el tamaño de
los cuerpos compilados. Devuelve `FourLeastModel { atoms, values, clauses,
entailed }`. Conserva las restricciones de `four.rs` (reglas ground,
argumentos constantes, un solo tiempo) salvo el límite de cuatro átomos.
`entailment`, `FourSession` y la salida de la CLI no cambian: la enumeración
sigue siendo la que cuenta `models` e `interpretations`, y el oráculo.

Verificación en `src/experiments/four_least_model_tests.rs`, tests
individuales con el runner:

- las 39 consultas `fourFusion` de las once fixtures: 8 se comparan y
  coinciden; 30 rechazadas por ambos evaluadores por reglas con parámetros y 1
  por argumentos o tiempos, con el mismo mensaje;
- 3.000 programas ground al azar (semilla fija, hasta cuatro átomos, cuerpos
  anidados arbitrarios construidos como TypedAST, `I` y literales negativos),
  con ambos resultados presentes: misma consecuencia que la enumeración;
- la contraposición de `four_counterexample.res`, con su modelo mínimo
  explícito, y una cadena de seis átomos que la enumeración rechaza.

**Integrado (2026-11-19).** `run_experiments` decide toda consulta
`fourFusion` con el modelo mínimo y añade la línea `FOUR least model` (valor
del objetivo, átomos, cláusulas). La enumeración se ejecuta solo con hasta
cuatro átomos, como comprobación, y conserva la línea `FOUR fusion`. Ambos
evaluadores, `FourSession` y el oráculo de tests reciben un `GroundProgram`,
que concentra las comprobaciones de groundness. Las reglas con parámetros se
instancian solo mediante `using`/`with`, con la resolución de bindings de las
consultas residuales; no hay grounding automático sobre las constantes del
módulo. Con ámbito, Horn observa las mismas instancias que FOUR. Un desacuerdo
entre el modelo mínimo y la enumeración es un error en toda compilación. Véase [FOUR con ámbito](executable-fixtures.md#four-con-ámbito-y-bindings-explícitos).
Las 30 consultas de fixtures con reglas parametrizadas siguen rechazadas con
un mensaje que remite a `using`/`with`; no se les añadieron bindings.

## Fuera de este inventario

Las eliminaciones y reemplazos (DRed, conteo de soportes) son una capacidad
nueva, no una optimización; siguen pendientes según el §4 de
[discrete-derivative.md](discrete-derivative.md).
