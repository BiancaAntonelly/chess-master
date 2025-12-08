package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

/**
 * Classe que representa um Cavalo no jogo de xadrez.
 * O cavalo move-se em forma de "L": duas casas em uma direção
 * e uma casa perpendicular, ou vice-versa.
 * O cavalo pode saltar sobre outras peças.
 */
public class Knight extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   assignable this.color, this.moveCount;
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
      @   pure
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
      @   // A posição atual do cavalo não é um movimento válido
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Movimentos em "L": (2,1) ou (1,2) de distância
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               (Math.abs(r - position.getRow()) == 2 && Math.abs(c - position.getCol()) == 1) ||
      @               (Math.abs(r - position.getRow()) == 1 && Math.abs(c - position.getCol()) == 2));
      @
      @   // Movimento 1: (-1, -2) - uma acima, duas esquerda
      @   ensures position.getRow() >= 1 && position.getCol() >= 2 &&
      @           canMove(new Position(position.getRow() - 1, position.getCol() - 2))
      @               ==> \result[position.getRow() - 1][position.getCol() - 2];
      @
      @   // Movimento 2: (-2, -1) - duas acima, uma esquerda
      @   ensures position.getRow() >= 2 && position.getCol() >= 1 &&
      @           canMove(new Position(position.getRow() - 2, position.getCol() - 1))
      @               ==> \result[position.getRow() - 2][position.getCol() - 1];
      @
      @   // Movimento 3: (-2, +1) - duas acima, uma direita
      @   ensures position.getRow() >= 2 && position.getCol() <= 6 &&
      @           canMove(new Position(position.getRow() - 2, position.getCol() + 1))
      @               ==> \result[position.getRow() - 2][position.getCol() + 1];
      @
      @   // Movimento 4: (-1, +2) - uma acima, duas direita
      @   ensures position.getRow() >= 1 && position.getCol() <= 5 &&
      @           canMove(new Position(position.getRow() - 1, position.getCol() + 2))
      @               ==> \result[position.getRow() - 1][position.getCol() + 2];
      @
      @   // Movimento 5: (+1, +2) - uma abaixo, duas direita
      @   ensures position.getRow() <= 6 && position.getCol() <= 5 &&
      @           canMove(new Position(position.getRow() + 1, position.getCol() + 2))
      @               ==> \result[position.getRow() + 1][position.getCol() + 2];
      @
      @   // Movimento 6: (+2, +1) - duas abaixo, uma direita
      @   ensures position.getRow() <= 5 && position.getCol() <= 6 &&
      @           canMove(new Position(position.getRow() + 2, position.getCol() + 1))
      @               ==> \result[position.getRow() + 2][position.getCol() + 1];
      @
      @   // Movimento 7: (+2, -1) - duas abaixo, uma esquerda
      @   ensures position.getRow() <= 5 && position.getCol() >= 1 &&
      @           canMove(new Position(position.getRow() + 2, position.getCol() - 1))
      @               ==> \result[position.getRow() + 2][position.getCol() - 1];
      @
      @   // Movimento 8: (+1, -2) - uma abaixo, duas esquerda
      @   ensures position.getRow() <= 6 && position.getCol() >= 2 &&
      @           canMove(new Position(position.getRow() + 1, position.getCol() - 2))
      @               ==> \result[position.getRow() + 1][position.getCol() - 2];
      @
      @   assignable \nothing;
      @   pure
      @*/
    @Override
    public /*@ pure non_null @*/ boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // Movimento 1: uma acima, duas esquerda (-1, -2)
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
      @   pure
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "N";
    }
}
