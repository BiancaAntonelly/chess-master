#!/bin/bash
# Script para verificar ChessPosition.java com OpenJML

echo "=== Verificando ChessPosition.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/chess/ChessException.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/chess/ChessPosition.java 2>&1 | \
    grep -E "(ChessPosition\.java|verify:|error:|warning:)" | \
    grep -A 5 "ChessPosition\.java"

echo ""
echo "=== Fim da verificação de ChessPosition.java ==="

