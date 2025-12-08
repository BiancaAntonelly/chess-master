#!/bin/bash
# Script para atualizar todos os scripts de verificação com indicadores visuais

# Lista de classes e suas dependências
declare -A classes=(
    ["Position"]="src/main/java/boardgame/Position.java"
    ["BoardException"]="src/main/java/boardgame/BoardException.java"
    ["Board"]="src/main/java/boardgame/Position.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Board.java"
    ["Piece"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java"
    ["Color"]="src/main/java/chess/Color.java"
    ["ChessException"]="src/main/java/boardgame/BoardException.java src/main/java/chess/ChessException.java"
    ["ChessPosition"]="src/main/java/boardgame/Position.java src/main/java/chess/ChessException.java src/main/java/boardgame/BoardException.java src/main/java/chess/ChessPosition.java"
    ["ChessPiece"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java"
    ["Bishop"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Bishop.java"
    ["Queen"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Queen.java"
    ["Knight"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Knight.java"
    ["Rook"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Rook.java"
    ["King"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Rook.java src/main/java/chess/ChessMatch.java src/main/java/chess/pieces/King.java"
    ["Pawn"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/ChessMatch.java src/main/java/chess/pieces/Pawn.java"
    ["ChessMatch"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/pieces/Bishop.java src/main/java/chess/pieces/King.java src/main/java/chess/pieces/Knight.java src/main/java/chess/pieces/Pawn.java src/main/java/chess/pieces/Queen.java src/main/java/chess/pieces/Rook.java src/main/java/chess/ChessMatch.java"
    ["UI"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/ChessMatch.java src/main/java/chess/pieces/Bishop.java src/main/java/chess/pieces/King.java src/main/java/chess/pieces/Knight.java src/main/java/chess/pieces/Pawn.java src/main/java/chess/pieces/Queen.java src/main/java/chess/pieces/Rook.java src/main/java/app/UI.java"
    ["Main"]="src/main/java/boardgame/Position.java src/main/java/boardgame/Board.java src/main/java/boardgame/BoardException.java src/main/java/boardgame/Piece.java src/main/java/chess/Color.java src/main/java/chess/ChessPosition.java src/main/java/chess/ChessException.java src/main/java/chess/ChessPiece.java src/main/java/chess/ChessMatch.java src/main/java/chess/pieces/Bishop.java src/main/java/chess/pieces/King.java src/main/java/chess/pieces/Knight.java src/main/java/chess/pieces/Pawn.java src/main/java/chess/pieces/Queen.java src/main/java/chess/pieces/Rook.java src/main/java/app/UI.java src/main/java/app/Main.java"
)

# Template para o script
generate_script() {
    local class_name=$1
    local dependencies=$2
    local file_path="scripts/verify_${class_name}.sh"
    
    cat > "$file_path" << EOF
#!/bin/bash
# Script para verificar ${class_name}.java com OpenJML

CLASS_NAME="${class_name}"
echo "=========================================="
echo "🔍 Verificando \${CLASS_NAME}.java"
echo "=========================================="
echo ""

STEP=1
TOTAL_STEPS=3

echo "[\$STEP/\$TOTAL_STEPS] 📦 Carregando dependências..."
STEP=\$((STEP + 1))

echo "[\$STEP/\$TOTAL_STEPS] ⚙️  Executando OpenJML..."
STEP=\$((STEP + 1))

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Resultados da Verificação:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

openjml --esc --progress -classpath src/main/java \\
    ${dependencies} 2>&1 | \\
    tee /tmp/jml_output_\${CLASS_NAME}.log | \\
    grep --line-buffered -E "(\${CLASS_NAME}\\.java|verify:|error:|warning:)" | \\
    grep -E "(\${CLASS_NAME}\\.java|verify:|error:|warning:)" | \\
    sed 's/^/  │ /' || true

echo ""
echo "[\$STEP/\$TOTAL_STEPS] ✅ Verificação concluída!"
echo ""

ERRORS=\$(grep -c "error:" /tmp/jml_output_\${CLASS_NAME}.log 2>/dev/null || echo "0")
WARNINGS=\$(grep -c "warning:" /tmp/jml_output_\${CLASS_NAME}.log 2>/dev/null || echo "0")
VERIFY_ISSUES=\$(grep -c "verify:" /tmp/jml_output_\${CLASS_NAME}.log 2>/dev/null || echo "0")

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📈 Estatísticas:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  🔴 Erros:     \$ERRORS"
echo "  🟡 Avisos:    \$WARNINGS"
echo "  🔵 Verificações: \$VERIFY_ISSUES"
echo ""

if [ "\$ERRORS" -eq "0" ] && [ "\$VERIFY_ISSUES" -eq "0" ]; then
    echo "✨ \${CLASS_NAME}.java: VERIFICAÇÃO BEM-SUCEDIDA!"
else
    echo "⚠️  \${CLASS_NAME}.java: Encontrados problemas (veja acima)"
fi

echo ""
echo "=========================================="
echo "🏁 Fim da verificação de \${CLASS_NAME}.java"
echo "=========================================="
echo ""
EOF

    chmod +x "$file_path"
    echo "✅ Atualizado: $file_path"
}

# Atualiza todos os scripts
for class in "${!classes[@]}"; do
    generate_script "$class" "${classes[$class]}"
done

echo ""
echo "✨ Todos os scripts foram atualizados com indicadores visuais!"

