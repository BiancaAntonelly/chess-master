#!/bin/bash
# Script para verificar BoardException.java com OpenJML

# Obtém o diretório do script
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

CLASS_NAME="BoardException"
echo "=== Verificando ${CLASS_NAME}.java ==="
echo ""

cd "$PROJECT_ROOT"

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/BoardException.java 2>&1 | \
    bash "$SCRIPT_DIR/filter_output.sh" "${CLASS_NAME}" || true

echo ""
echo "=== Fim da verificação de ${CLASS_NAME}.java ==="
