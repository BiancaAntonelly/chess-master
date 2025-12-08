#!/bin/bash
# Script para executar todos os scripts de verificação

echo "=========================================="
echo "Executando todas as verificações OpenJML"
echo "=========================================="
echo ""

SCRIPTS_DIR="$(cd "$(dirname "$0")" && pwd)"

# Lista de todos os scripts de verificação
scripts=(
    "verify_Position.sh"
    "verify_BoardException.sh"
    "verify_Board.sh"
    "verify_Piece.sh"
    "verify_Color.sh"
    "verify_ChessException.sh"
    "verify_ChessPosition.sh"
    "verify_ChessPiece.sh"
    "verify_Bishop.sh"
    "verify_Queen.sh"
    "verify_Knight.sh"
    "verify_Rook.sh"
    "verify_King.sh"
    "verify_Pawn.sh"
    "verify_ChessMatch.sh"
    "verify_UI.sh"
    "verify_Main.sh"
)

# Executa cada script
for script in "${scripts[@]}"; do
    if [ -f "$SCRIPTS_DIR/$script" ]; then
        echo ""
        echo ">>> Executando $script <<<"
        echo ""
        bash "$SCRIPTS_DIR/$script"
        echo ""
        echo "---"
    else
        echo "Aviso: Script $script não encontrado"
    fi
done

echo ""
echo "=========================================="
echo "Todas as verificações concluídas"
echo "=========================================="

