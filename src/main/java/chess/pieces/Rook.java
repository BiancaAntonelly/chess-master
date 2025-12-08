package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Rook extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getBoard() == board;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   assignable this.*;
      @*/
    public Rook(Board board, Color color) {
        super(board, color);
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("R");
      @   assignable \nothing;
      @   pure
      @*/
    @Override
    public String toString() {
        return "R";
    }

    /*@ also
      @ public normal_behavior
      @   // a posição atual da peça deve ser válida no tabuleiro
      @   requires position != null;
      @   requires 0 <= position.getRow() && position.getRow() < getBoard().getRows();
      @   requires 0 <= position.getCol() && position.getCol() < getBoard().getCols();
      @
      @   // matriz de movimentos bem formada, do tamanho do tabuleiro
      @   ensures \result != null;
      @   ensures \result.length == getBoard().getRows();
      @   ensures (\forall int i; 0 <= i && i < getBoard().getRows();
      @               \result[i] != null && \result[i].length == getBoard().getCols());
      @
      @   // qualquer casa marcada como possível movimento está na mesma linha ou coluna da torre
      @   ensures (\forall int r,c;
      @               0 <= r && r < getBoard().getRows() &&
      @               0 <= c && c < getBoard().getCols();
      @               \result[r][c] ==> (r == position.getRow() || c == position.getCol()));
      @
      @   // a própria casa da torre nunca é marcada como movimento
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];
        Position p = new Position(0, 0);

        // Para cima
        p.setValues(position.getRow() - 1, position.getCol());
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para a esquerda
        p.setValues(position.getRow(), position.getCol() - 1);
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para a direita
        p.setValues(position.getRow(), position.getCol() + 1);
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para baixo
        p.setValues(position.getRow() + 1, position.getCol());
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        return mat;
    }
}
