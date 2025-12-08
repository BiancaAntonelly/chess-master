#!/bin/bash
# Script para verificar Board.java com OpenJML

echo "=== Verificando Board.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Board.java 2>&1 | \
    bash scripts/filter_output.sh "Board"

echo ""
echo "=== Fim da verificação de Board.java ==="

