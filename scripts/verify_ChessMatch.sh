#!/bin/bash
# Script para verificar ChessMatch.java com OpenJML

echo "=== Verificando ChessMatch.java ==="
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
    src/main/java/chess/pieces/Bishop.java \
    src/main/java/chess/pieces/King.java \
    src/main/java/chess/pieces/Knight.java \
    src/main/java/chess/pieces/Pawn.java \
    src/main/java/chess/pieces/Queen.java \
    src/main/java/chess/pieces/Rook.java \
    src/main/java/chess/ChessMatch.java 2>&1 | \
    bash scripts/filter_output.sh "ChessMatch"

echo ""
echo "=== Fim da verificação de ChessMatch.java ==="

