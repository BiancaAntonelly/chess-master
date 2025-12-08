#!/bin/bash
# Script para verificar BoardException.java com OpenJML

echo "=== Verificando BoardException.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/BoardException.java 2>&1 | \
    grep -E "(BoardException\.java|verify:|error:|warning:)" | \
    grep -A 5 "BoardException\.java"

echo ""
echo "=== Fim da verificação de BoardException.java ==="

