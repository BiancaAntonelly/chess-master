#!/bin/bash
# Script para verificar Pawn.java com OpenJML

echo "=== Verificando Pawn.java ==="
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
    src/main/java/chess/ChessMatch.java \
    src/main/java/chess/pieces/Pawn.java 2>&1 | \
    grep -E "(Pawn\.java|verify:|error:|warning:)" | \
    grep -A 5 "Pawn\.java"

echo ""
echo "=== Fim da verificação de Pawn.java ==="

