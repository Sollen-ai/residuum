# Coste de compilación de los targets de tests y palancas posibles

Inventario de 2026-11-01. Complementa
[residual-compilation-cost.md](residual-compilation-cost.md), que fijó el
presupuesto de verificación, y lo corrige en un punto: el pico de memoria al
compilar es memoria de trabajo del compilador, no caché de archivos. Este
documento mide, ordena palancas y registra la única aplicada: `debug = 0` en
el perfil `test` de `Cargo.toml`. No modifica el runner, sus límites ni sus
controles.

## Qué problema es y a quién afecta

`scripts/test_safe.py` compila y ejecuta dentro de un cgroup de 1 GiB sin swap,
con un trabajo de Cargo y `CPUQuota=100%`. Además detiene preventivamente
cualquier etapa cuyo cgroup alcance `STOP_MEMORY`, 768 MiB. Ése es el tope
efectivo.

Ejecutar un programa `.res` no está afectado. La vía `--fixture x.res --cli run`
compila el binario `residuum` con `cargo build`, sin código de tests, en menos de
400 MiB; si nada cambió, Cargo lo reutiliza en 0,06 s. El tope lo rozan sólo los
dos targets de tests, `--test-target lib` y `--test-target cli`, porque Cargo
compila todos los tests del target en un único binario aunque se vaya a ejecutar
uno solo.

El 2026-11-01 a las 19:30 UTC dos compilaciones de tests fueron detenidas por
`near_memory_limit` con picos de cgroup de 807 y 811 MiB; las dos siguientes
pasaron con 733 y 767 MiB. La falla es intermitente y empeora con cada test que
se añade.

## Tamaño de lo que se compila

| Parte | Líneas |
|---|---:|
| Biblioteca sin tests | 15 263 |
| Tests de la biblioteca (`cfg(test)`, incluidos 3 700 inline en `lib.rs`) | ≈ 14 100 |
| Código de la CLI | 1 347 |
| Tests de la CLI, 26 módulos bajo `cli.rs:225` | 21 791 |
| Total | 52 549 |

Dos de cada tres líneas son tests. El crate de tests de la CLI es un 94 % tests.

## Mediciones

Toolchain rustc 1.87.0, 16 CPU con cuota de uno, cgroup v2. Todas las filas se
obtuvieron con el runner, sin variables salvo las indicadas, leyendo
`cgroup_peak_bytes` y `peak_rss_bytes` del informe. Las columnas anónima y caché
provienen de un muestreador externo de `memory.stat` cada 30 ms sobre el scope,
así que son cotas inferiores del máximo real. "Desde cero" significa sin
directorio incremental previo del crate; las dependencias ya estaban compiladas.

| Caso | Target | Pico cgroup (MiB) | Anónima | Caché | Tiempo |
|---|---|---:|---:|---:|---:|
| `debug=2`, incremental, desde cero | lib | detenido ≥ 772 | 698 | 52 | — |
| `debug=0`, incremental, desde cero | lib | 684 | 552 | 114 | 11,7 s |
| `debug=0`, sin incremental | lib | 619 | — | — | 9,7 s |
| `debug=0`, sin incremental, `codegen-units=16` | lib | 646 | — | — | 13,0 s |
| `debug=0`, sin incremental, `codegen-units=1` | lib | detenido ≥ 770 | — | — | — |
| `debug=0`, incremental, sólo `touch` | lib | 413 | — | — | 1,8 s |
| `debug=0`, incremental, edición real pequeña | lib | 419 | 312 | 82 | 1,7 s |
| `debug=0`, sin incremental | cli | 561 | — | — | 12,3 s |
| `debug=0`, incremental, sólo `touch` | cli | 455 | — | — | 2,1 s |
| `debug=0`, biblioteca sin tests + example, desde cero | run_fixture | ≤ 396 | 341 | 83 | 6,8 s |
| Perfil `test` con `debug = 0` aplicado, sin variables, desde cero | lib | 675 | — | — | 11,5 s |
| Perfil `test` con `debug = 0` aplicado, sin variables | cli | 651 | — | — | 8,7 s |

La fila de `run_fixture` incluye la recompilación de las dependencias por cambio
de perfil `dev`; su pico puede corresponder a zerocopy y no a la biblioteca, por
eso es una cota superior.

## Lo que se concluye

1. **La memoria es anónima.** La caché de archivos es del 8 al 17 % del pico.
   Excluirla de la métrica del runner o forzar su recuperación compraría a lo
   sumo 50 a 110 MiB. No es la palanca principal.
2. **El tamaño del crate de tests es el coste.** La biblioteca sola cabe por
   debajo de 400 MiB; con sus tests sube a 620 o 700; la CLI con sus tests, a
   560 o 800.
3. **`debug=0` es necesario y no debe depender de una variable.** Es la diferencia
   entre detenerse por encima de 772 y caber en 684.
4. **Incremental se conserva.** Cuesta 65 MiB en la compilación desde cero y
   ahorra 200 MiB y ocho segundos en la edición típica.
5. **`codegen-units` no ayuda.** Reducirlas sube el pico; con una CPU de cuota
   tampoco hay ganancia de tiempo por paralelismo.

## Palancas, por orden de recomendación

| # | Palanca | Efecto esperado | Riesgo | Estado |
|---:|---|---|---|---|
| 1 | `[profile.test] debug = 0` en `Cargo.toml` | ≥ 772 → 675 en lib; deja de depender del entorno | Ninguno | **Aplicada** |
| 2 | Agrupar módulos de test por familias tras features de Cargo | Cada compilación se acerca a biblioteca + una familia, ≈ 400 a 500 | Bajo; `test_safe.py` debe aceptar `--features` y seguir exigiendo un binario | **Aplicada** (véase abajo) |
| 3 | Fixtures ejecutadas por la CLI con salida esperada, en vez de tests Rust que sólo cargan un `.res` | Los 133 tests que cargan fixtures salen del crate de la CLI | Medio: requiere salida JSON estable y resolver `derivedAt` | Pendiente |
| 4 | Mover la lógica de la CLI a la biblioteca y los tests a `tests/` como crates de integración | Igual que 2 con compilación separada por archivo | Medio: refactor de 1 347 líneas | Alternativa a 2 |
| 5 | Separar los experimentos jurídicos en un crate del workspace | Reduce también el crate de biblioteca | Alto esfuerzo | Pendiente |
| 6 | Fijar `ahash` a 0.8.6 para eliminar zerocopy, zerocopy-derive, syn, quote y proc-macro2 | Sólo compilaciones limpias; cinco crates menos | Bajo; necesita red, 0.8.6 no está en la caché del registro | Pendiente |
| 7 | `MemoryHigh` en el scope para recuperar caché antes del tope | 50 a 110 MiB | Es un cambio de controles; decisión del propietario | No propuesta |

Los 362 tests que construyen su entrada en Rust y comprueban internals (leyes
algebraicas, bindings residuales, contadores del cierre incremental, igualdad de
provenance, errores de elaboración) seguirán en Rust. Para ellos valen las
palancas 1, 2 y 5. Los oráculos independientes que hoy viven en código de test
(saturación por bitsets, enumeración exhaustiva, `linear_scan`) necesitan un
destino antes de la palanca 3: subcomandos experimentales de la CLI o scripts en
Python como `scripts/four_least_model_check.py`.

## Descartadas con medición

- `codegen-units = 1`: detenida por encima de 770 MiB.
- `codegen-units = 16`: 646 frente a 619 del valor por defecto.
- Desactivar incremental de forma permanente: ahorra 65 MiB sólo en la
  compilación desde cero y multiplica por cinco el tiempo de la edición típica.

## Límites de estas mediciones

- Las detenciones de las 19:30 UTC alcanzaron 807 y 811 MiB, por encima de lo
  reproducido aquí en condiciones equivalentes. Puede ser variación entre
  ejecuciones o un perfil distinto. El informe del runner no registra el entorno
  del perfil, así que no se puede saber. Conviene que lo registre.
- El muestreador externo corre a 30 ms; el pico del cgroup del informe es más
  preciso que sus columnas anónima y caché.
- No se midió `debug = "line-tables-only"`, punto medio si hacen falta trazas.
- Las cifras dependen de rustc 1.87.0 y del estado actual del código; crecerán con
  cada test que se añada; la palanca 2 permite compilar sólo una familia.

## Cambio aplicado

`Cargo.toml` añade `[profile.test] debug = 0`. Verificación: compilación de los
dos targets de tests sin variables de entorno, 675 y 651 MiB, y un test de la
biblioteca ejecutado individualmente con el binario nuevo. El perfil `dev`, con
el que se compila el binario `residuum`, no cambia.

## Palanca 2 aplicada: familias de tests

`Cargo.toml` declara las features `test-core`, `test-residual`,
`test-experiments`, `test-legal-geometry` y `test-legal-learning`; cada una
activa el marcador `test-families`. `build.rs`, sin dependencias, emite un cfg
`family_*` por familia seleccionada, o todos si no se selecciona ninguna. Así
`cargo test` sin features compila exactamente los mismos tests que antes.

| Familia | Target | Módulos |
|---|---|---|
| núcleo (siempre) | lib | `lib.rs` en línea, `derive`, `algebra`, `formal`, identidad de eventos, términos temporales, regresión monótona |
| `test-residual` | lib | todo `src/residual/**` |
| `test-experiments` | lib | todo `src/experiments/**` y `legal_abduction_tests` |
| núcleo (siempre) | cli | todos los módulos de `cli/tests.rs` salvo los jurídicos, y `cli/steps` |
| `test-legal-geometry` | cli | `legal_geometry` base (sus siete tests), extremos, fronteras, residual, consultas, activación, particiones, revisión de regiones; `legal_partition` |
| `test-legal-learning` | cli | recalcitrancia, conversación, explicaciones tipadas, Riggs, generación estructural (más los helpers de la base, sin sus tests) |

El runner acepta `--features=a,b`, rechaza nombres desconocidos, la pasa a
`cargo test --no-run` y sigue exigiendo un único binario. Ejemplo:

```
python3 scripts/test_safe.py --test-target cli --features=test-legal-learning --test <nombre>
```

Medición del 2026-11-18, perfil `test` con `debug = 0`, compilación de
`residuum` desde cero con dependencias ya compiladas, en dos condiciones: con
`CARGO_INCREMENTAL=0` y con los valores por defecto del runner (incremental
activo, tras borrar `target/debug/incremental/residuum-*`). Tests activos
contados con `--list` a través del runner:

| Selección | Target | Pico cgroup, sin incremental (MiB) | Pico cgroup, runner por defecto (MiB) | Tests activos |
|---|---|---:|---:|---:|
| todas (sin features) | lib | 582 | 676 | 291 |
| `test-core` | lib | 471 | 526 | 149 |
| `test-residual` | lib | 510 | 590 | 222 |
| `test-experiments` | lib | 552 | 616 | 218 |
| todas (sin features) | cli | 575 | 734 | 195 |
| `test-core` | cli | 373 | 460 | 122 |
| `test-legal-geometry` | cli | 521 | 624 | 174 |
| `test-legal-learning` | cli | 444 | 583 | 143 |

Las compilaciones por familia no emiten avisos en ninguna de las dos
condiciones. La unión de los nombres de las familias de cada target es igual,
test por test, al conjunto sin features; ningún test se pierde ni se duplica
entre familias. Sin features la biblioteca midió 582 frente a 614 y 619 en
otras ejecuciones del mismo caso: la variación entre corridas es de unos
40 MiB, del mismo orden que algunas diferencias de la tabla. Con los valores
por defecto del runner, que es como se compila de ordinario, el ahorro es de
unos 85 a 150 MiB en la biblioteca y de 110 a 275 en la CLI;
`test-experiments` y `test-legal-geometry` quedan unos 150 MiB bajo el freno
de 768, frente a 92 y 34 sin features.

El runner rechaza una familia que no tiene tests en el target elegido (por
ejemplo `--test-target lib --features=test-legal-geometry`): compilaría sólo
el núcleo, y sin `--test` se ejecutarían los tests del núcleo como si la
familia estuviera incluida.
