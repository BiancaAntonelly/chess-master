#!/bin/bash
# Script para verificar Piece.java com OpenJML

echo "=== Verificando Piece.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Piece.java 2>&1 | \
    bash scripts/filter_output.sh "Piece"

echo ""
echo "=== Fim da verificação de Piece.java ==="

