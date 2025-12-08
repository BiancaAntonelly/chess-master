#!/bin/bash
# Script para verificar Queen.java com OpenJML

echo "=== Verificando Queen.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Piece.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessException.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Queen.java 2>&1 | \
    grep -E "(Queen\.java|verify:|error:|warning:)" | \
    grep -A 5 "Queen\.java"

echo ""
echo "=== Fim da verificação de Queen.java ==="

