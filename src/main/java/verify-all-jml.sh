#!/bin/bash

# Script para verificação completa de todas as especificações JML
# Documentação JML Máxima - Projeto Chess Master

echo "=========================================="
echo "Verificação Completa OpenJML"
echo "Especificação Máxima - Todas as Classes"
echo "=========================================="
echo ""

# Cores para output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Diretório base
BASE_DIR="/mnt/c/Users/humbe/.claude-worktrees/chess-master/wonderful-feistel"
cd "$BASE_DIR" || exit 1

echo "Diretório: $BASE_DIR"
echo ""

# Função para verificar um conjunto de arquivos
verify_files() {
    local description=$1
    shift
    local files=("$@")

    echo -e "${YELLOW}=== $description ===${NC}"

    # Executar OpenJML com timeout
    timeout 180 openjml --esc --progress --timeout=60 -classpath . "${files[@]}" 2>&1

    local exit_code=$?

    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}✅ $description: SUCESSO${NC}"
        return 0
    elif [ $exit_code -eq 124 ]; then
        echo -e "${RED}⏱️  $description: TIMEOUT (>3 minutos)${NC}"
        return 1
    else
        echo -e "${RED}❌ $description: FALHOU${NC}"
        return 1
    fi

    echo ""
}

# Contador de sucessos/falhas
SUCCESS=0
FAILED=0

echo "=========================================="
echo "FASE 1: Classes Base"
echo "=========================================="
echo ""

verify_files "Color e ChessException" \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessException.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "FASE 2: ChessPosition"
echo "=========================================="
echo ""

verify_files "ChessPosition" \
    src/main/java/boardgame/Position.java \
    src/main/java/chess/ChessPosition.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "FASE 3: ChessPiece (abstrata)"
echo "=========================================="
echo ""

verify_files "ChessPiece" \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Piece.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessPiece.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "FASE 4: Peças de Xadrez"
echo "=========================================="
echo ""

verify_files "King" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/ChessMatch.java \
    src/main/java/chess/pieces/King.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

verify_files "Queen" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Queen.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

verify_files "Rook" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Rook.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

verify_files "Bishop" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Bishop.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

verify_files "Knight" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Knight.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

verify_files "Pawn" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/ChessMatch.java \
    src/main/java/chess/pieces/Pawn.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "FASE 5: ChessMatch (pode ser lento)"
echo "=========================================="
echo ""

verify_files "ChessMatch" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessException.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/*.java \
    src/main/java/chess/ChessMatch.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "FASE 6: Verificação Completa (TUDO)"
echo "=========================================="
echo ""

verify_files "TODAS AS CLASSES" \
    src/main/java/boardgame/*.java \
    src/main/java/chess/*.java \
    src/main/java/chess/pieces/*.java

if [ $? -eq 0 ]; then ((SUCCESS++)); else ((FAILED++)); fi

echo ""
echo "=========================================="
echo "RESUMO FINAL"
echo "=========================================="
echo ""
echo -e "${GREEN}Sucessos: $SUCCESS${NC}"
echo -e "${RED}Falhas: $FAILED${NC}"
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}🎉 TODAS AS VERIFICAÇÕES PASSARAM! 🎉${NC}"
    exit 0
else
    echo -e "${YELLOW}⚠️  Algumas verificações falharam ou tiveram timeout${NC}"
    echo -e "${YELLOW}Isso é esperado para verificações complexas${NC}"
    exit 1
fi
