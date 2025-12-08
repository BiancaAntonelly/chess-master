#!/bin/bash
# Script para verificar ChessPiece.java com OpenJML

echo "=== Verificando ChessPiece.java ==="
echo ""

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Piece.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessException.java \
    src/main/java/chess/ChessPiece.java 2>&1 | \
    bash scripts/filter_output.sh "ChessPiece"

echo ""
echo "=== Fim da verificação de ChessPiece.java ==="

