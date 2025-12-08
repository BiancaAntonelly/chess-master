#!/bin/bash
# Script para verificar ChessException.java com OpenJML

echo "=== Verificando ChessException.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/chess/ChessException.java 2>&1 | \
    grep -E "(ChessException\.java|verify:|error:|warning:)" | \
    grep -A 5 "ChessException\.java"

echo ""
echo "=== Fim da verificação de ChessException.java ==="

