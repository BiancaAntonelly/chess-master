#!/bin/bash
# Script para verificar Position.java com OpenJML

echo "=== Verificando Position.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java 2>&1 | \
    grep -E "(Position\.java|verify:|error:|warning:)" | \
    grep -A 5 "Position\.java"

echo ""
echo "=== Fim da verificação de Position.java ==="

