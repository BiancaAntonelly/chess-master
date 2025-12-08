#!/bin/bash
# Script para verificar Color.java com OpenJML

echo "=== Verificando Color.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/chess/Color.java 2>&1 | \
    grep -E "(Color\.java|verify:|error:|warning:)" | \
    grep -A 5 "Color\.java"

echo ""
echo "=== Fim da verificação de Color.java ==="

