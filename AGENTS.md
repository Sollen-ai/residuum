# Verificación y alcance

- Usa `python3 scripts/test_safe.py` para compilación y tests. No ejecutes
  `cargo test` directamente ni binarios de tests fuera del runner con límites.
- Respeta la autorización vigente: seleccionar tests individuales no autoriza
  ejecutar todos los tests, con o sin paralelismo.
- Mantén 1324 MiB total (1 GiB + 300 MiB, autorizado por el propietario el
  2026-11-19), sin swap, un trabajo de Cargo y un hilo del harness. No eleves
  más los límites ni desactives los controles para conseguir un resultado verde.
- El runner falla si no puede crear/verificar el cgroup. Resuelve el acceso a
  systemd mediante la aprobación del entorno; no uses una alternativa sin límites.
- CNL está conservado y pausado como frontend. Sus tests `ignored` no son criterio
  de cierre. El pipeline activo es Formal → SurfaceAST → TypedAST → derivation/runtime.
- Un drafter TypedAST → CNL/legal prose es trabajo futuro; no está implementado.
