#!/bin/bash
# Script para atualizar todos os scripts de verificação com caminhos corretos

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Função para atualizar um script
update_script() {
    local script_file="$1"
    local class_name="$2"
    
    # Adiciona cabeçalho com caminhos corretos se não existir
    if ! grep -q "SCRIPT_DIR=" "$script_file"; then
        # Insere após a linha do shebang
        sed -i '2a\
# Obtém o diretório do script\
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"\
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"' "$script_file"
    fi
    
    # Substitui caminhos relativos por absolutos
    sed -i "s|bash scripts/filter_output.sh|bash \"\$SCRIPT_DIR/filter_output.sh\"|g" "$script_file"
    sed -i "s|bash \"scripts/filter_output.sh\"|bash \"\$SCRIPT_DIR/filter_output.sh\"|g" "$script_file"
    
    # Adiciona cd para project root antes do openjml se não existir
    if ! grep -q "cd \"\$PROJECT_ROOT\"" "$script_file"; then
        sed -i '/openjml --esc/i\
cd "$PROJECT_ROOT"' "$script_file"
    fi
    
    # Corrige contagem de erros
    sed -i 's/ERRORS=$(grep -c "error:"/ERRORS=$(grep -c "error:" \/tmp\/jml_output_${CLASS_NAME}.log 2>\/dev\/null | head -1 || echo "0")/g' "$script_file"
    sed -i 's/WARNINGS=$(grep -c "warning:"/WARNINGS=$(grep -c "warning:" \/tmp\/jml_output_${CLASS_NAME}.log 2>\/dev\/null | head -1 || echo "0")/g' "$script_file"
    sed -i 's/VERIFY_ISSUES=$(grep -c "verify:"/VERIFY_ISSUES=$(grep -c "verify:" \/tmp\/jml_output_${CLASS_NAME}.log 2>\/dev\/null | head -1 || echo "0")/g' "$script_file"
    
    # Adiciona limpeza de espaços antes da comparação
    if grep -q "if \[ \"\$ERRORS\"" "$script_file" && ! grep -q "ERRORS=\$(echo" "$script_file"; then
        sed -i '/if \[ "\$ERRORS"/i\
# Remove espaços e quebras de linha\
ERRORS=$(echo "$ERRORS" | tr -d " \\n")\
WARNINGS=$(echo "$WARNINGS" | tr -d " \\n")\
VERIFY_ISSUES=$(echo "$VERIFY_ISSUES" | tr -d " \\n")' "$script_file"
        sed -i 's/if \[ "\$ERRORS"/if [ "${ERRORS:-0}"/g' "$script_file"
        sed -i 's/&& \[ "\$VERIFY_ISSUES"/\&\& [ "${VERIFY_ISSUES:-0}"/g' "$script_file"
    fi
}

# Lista de scripts para atualizar
scripts=(
    "verify_BoardException.sh:BoardException"
    "verify_Board.sh:Board"
    "verify_Piece.sh:Piece"
    "verify_Color.sh:Color"
    "verify_ChessException.sh:ChessException"
    "verify_ChessPosition.sh:ChessPosition"
    "verify_ChessPiece.sh:ChessPiece"
    "verify_Bishop.sh:Bishop"
    "verify_Queen.sh:Queen"
    "verify_Knight.sh:Knight"
    "verify_Rook.sh:Rook"
    "verify_King.sh:King"
    "verify_Pawn.sh:Pawn"
    "verify_ChessMatch.sh:ChessMatch"
    "verify_UI.sh:UI"
    "verify_Main.sh:Main"
)

for entry in "${scripts[@]}"; do
    script="${entry%%:*}"
    class="${entry##*:}"
    if [ -f "$SCRIPT_DIR/$script" ]; then
        echo "Atualizando $script..."
        update_script "$SCRIPT_DIR/$script" "$class"
    fi
done

echo "Todos os scripts foram atualizados!"
