#!/bin/bash
# Script para verificar Board.java com OpenJML

echo "=== Verificando Board.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Board.java 2>&1 | \
    grep -E "(Board\.java|verify:|error:|warning:)" | \
    grep -A 5 "Board\.java"

echo ""
echo "=== Fim da verificação de Board.java ==="

