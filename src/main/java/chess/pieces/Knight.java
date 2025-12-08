package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Knight extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Knight(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
    }

    /*@ private normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   requires getBoard().positionExists(position);
      @   ensures \result == true ==> (getBoard().piece(position) == null ||
      @           ((ChessPiece)getBoard().piece(position)).getColor() != getColor());
      @   ensures \result == false ==> (getBoard().piece(position) != null &&
      @           ((ChessPiece)getBoard().piece(position)).getColor() == getColor());
      @   assignable \nothing;
      @*/
    private /*@ pure @*/ boolean canMove(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Sempre que uma casa é verdadeira, ela está em um padrão de movimento em L do cavalo
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               ((r == position.getRow() - 2 && c == position.getCol() - 1) ||
      @                (r == position.getRow() - 2 && c == position.getCol() + 1) ||
      @                (r == position.getRow() - 1 && c == position.getCol() - 2) ||
      @                (r == position.getRow() - 1 && c == position.getCol() + 2) ||
      @                (r == position.getRow() + 1 && c == position.getCol() - 2) ||
      @                (r == position.getRow() + 1 && c == position.getCol() + 2) ||
      @                (r == position.getRow() + 2 && c == position.getCol() - 1) ||
      @                (r == position.getRow() + 2 && c == position.getCol() + 1)));
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // Movimento em L: 8 direções possíveis
        p.setValues(position.getRow() - 1, position.getCol() - 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 2: duas acima, uma esquerda (-2, -1)
        p.setValues(position.getRow() - 2, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 3: duas acima, uma direita (-2, +1)
        p.setValues(position.getRow() - 2, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 4: uma acima, duas direita (-1, +2)
        p.setValues(position.getRow() - 1, position.getCol() + 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 5: uma abaixo, duas direita (+1, +2)
        p.setValues(position.getRow() + 1, position.getCol() + 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 6: duas abaixo, uma direita (+2, +1)
        p.setValues(position.getRow() + 2, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 7: duas abaixo, uma esquerda (+2, -1)
        p.setValues(position.getRow() + 2, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Movimento 8: uma abaixo, duas esquerda (+1, -2)
        p.setValues(position.getRow() + 1, position.getCol() - 2);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("N");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "N";
    }
}
