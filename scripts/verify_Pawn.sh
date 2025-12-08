#!/bin/bash
# Script para verificar Pawn.java com OpenJML

# Obtém o diretório do script
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

CLASS_NAME="Pawn"
echo "=== Verificando ${CLASS_NAME}.java ==="
echo ""

cd "$PROJECT_ROOT"

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
    bash "$SCRIPT_DIR/filter_output.sh" "${CLASS_NAME}" || true

echo ""
echo "=== Fim da verificação de Pawn.java ==="

