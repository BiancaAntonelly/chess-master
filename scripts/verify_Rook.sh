#!/bin/bash
# Script para verificar Rook.java com OpenJML

echo "=== Verificando Rook.java ==="
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
    src/main/java/chess/pieces/Rook.java 2>&1 | \
    bash scripts/filter_output.sh "Rook"

echo ""
echo "=== Fim da verificação de Rook.java ==="

