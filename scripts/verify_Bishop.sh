#!/bin/bash
# Script para verificar Bishop.java com OpenJML

echo "=== Verificando Bishop.java ==="
echo ""

# Executa OpenJML e filtra apenas resultados relacionados a Bishop.java
openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Piece.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessException.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Bishop.java 2>&1 | \
    grep --line-buffered -E "(Bishop\.java|verify:|error:|warning:)" | \
    grep -E "(Bishop\.java|verify:|error:|warning:)" | \
    sed 's/^/  /'

echo ""
echo "=== Fim da verificação de Bishop.java ==="
