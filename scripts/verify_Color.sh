#!/bin/bash
# Script para verificar Color.java com OpenJML

echo "=== Verificando Color.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/chess/Color.java 2>&1 | \
    bash scripts/filter_output.sh "Color"

echo ""
echo "=== Fim da verificação de Color.java ==="

