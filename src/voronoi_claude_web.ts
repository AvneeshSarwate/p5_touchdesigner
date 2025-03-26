// Voronoi.ts - TypeScript implementation of Fortune's algorithm
// Based on Raymond Hill's JavaScript implementation
// MIT License: See https://github.com/gorhill/Javascript-Voronoi/LICENSE.md

/**
 * Interface for a site in the Voronoi diagram
 */
interface Site {
  x: number;
  y: number;
  voronoiId?: number;
}

/**
 * Interface for a bounding box
 */
interface BBox {
  xl: number; // x left
  xr: number; // x right
  yt: number; // y top
  yb: number; // y bottom
}

/**
 * Interface for a Voronoi diagram
 */
interface VDiagram {
  cells: VCell[];
  edges: any[];
  vertices: any[];
  execTime: number;
}

/**
 * Interface for a Voronoi cell
 */
interface VCell {
  site: VSite;
  halfedges: VHalfedge[];
  prepareHalfedges(): number;
  closeMe: boolean;
}

/**
 * Interface for a Voronoi site
 */
interface VSite {
  x: number;
  y: number;
  voronoiId: number;
}

/**
 * Interface for a Voronoi halfedge
 */
interface VHalfedge {
  getStartpoint(): { x: number, y: number };
  getEndpoint(): { x: number, y: number };
}

/**
 * Voronoi class for generating Voronoi diagrams
 */
class Voronoi {
  private vertices: any[] | null;
  private edges: any[] | null;
  private cells: any[] | null;
  private toRecycle: any;
  private beachsectionJunkyard: any[];
  private circleEventJunkyard: any[];
  private vertexJunkyard: any[];
  private edgeJunkyard: any[];
  private cellJunkyard: any[];
  private beachline: any;
  private circleEvents: any;
  private firstCircleEvent: any;
  
  // Mathematical constants and utilities
  private readonly sqrt = Math.sqrt;
  private readonly abs = Math.abs;
  private readonly ε = 1e-9;
  private readonly invε = 1.0 / this.ε;

  /**
   * Create a new Voronoi instance
   */
  constructor() {
    this.vertices = null;
    this.edges = null;
    this.cells = null;
    this.toRecycle = null;
    this.beachsectionJunkyard = [];
    this.circleEventJunkyard = [];
    this.vertexJunkyard = [];
    this.edgeJunkyard = [];
    this.cellJunkyard = [];
  }

  /**
   * Reset the Voronoi instance
   */
  reset(): void {
    if (!this.beachline) {
      this.beachline = new this.RBTree();
    }
    // Move leftover beachsections to the beachsection junkyard.
    if (this.beachline.root) {
      let beachsection = this.beachline.getFirst(this.beachline.root);
      while (beachsection) {
        this.beachsectionJunkyard.push(beachsection); // mark for reuse
        beachsection = beachsection.rbNext;
      }
    }
    this.beachline.root = null;
    if (!this.circleEvents) {
      this.circleEvents = new this.RBTree();
    }
    this.circleEvents.root = this.firstCircleEvent = null;
    this.vertices = [];
    this.edges = [];
    this.cells = [];
  }

  /**
   * Compare values with epsilon for floating-point precision
   */
  equalWithEpsilon(a: number, b: number): boolean {
    return this.abs(a - b) < 1e-9;
  }

  greaterThanWithEpsilon(a: number, b: number): boolean {
    return a - b > 1e-9;
  }

  greaterThanOrEqualWithEpsilon(a: number, b: number): boolean {
    return b - a < 1e-9;
  }

  lessThanWithEpsilon(a: number, b: number): boolean {
    return b - a > 1e-9;
  }

  lessThanOrEqualWithEpsilon(a: number, b: number): boolean {
    return a - b < 1e-9;
  }

  /**
   * Red-Black Tree implementation
   */
  RBTree = function(this: any) {
    this.root = null;
  };

  /**
   * Insert a successor node in the RB-Tree
   */
  private rbInsertSuccessor(node: any, successor: any): void {
    let parent = node;
    // rhill 2011-06-07: if node is null, successor must be inserted
    // to the left-most part of the tree
    if (parent) {
      successor.rbPrevious = parent;
      successor.rbNext = parent.rbNext;
      if (parent.rbNext) {
        parent.rbNext.rbPrevious = successor;
      }
      parent.rbNext = successor;
      if (parent.rbRight) {
        parent = parent.rbRight;
        while (parent.rbLeft) {
          parent = parent.rbLeft;
        }
        parent.rbLeft = successor;
      } else {
        parent.rbRight = successor;
      }
    } else if (this.beachline.root) {
      let node = this.beachline.getFirst(this.beachline.root);
      successor.rbPrevious = null;
      successor.rbNext = node;
      node.rbPrevious = successor;
      node.rbLeft = successor;
      parent = node;
    } else {
      successor.rbPrevious = successor.rbNext = null;
      this.beachline.root = successor;
      parent = null;
    }
    successor.rbLeft = successor.rbRight = null;
    successor.rbParent = parent;
    successor.rbRed = true;
    
    // Rebalance the tree
    let grandpa, uncle;
    node = successor;
    while (parent && parent.rbRed) {
      grandpa = parent.rbParent;
      if (parent === grandpa.rbLeft) {
        uncle = grandpa.rbRight;
        if (uncle && uncle.rbRed) {
          parent.rbRed = uncle.rbRed = false;
          grandpa.rbRed = true;
          node = grandpa;
        } else {
          if (node === parent.rbRight) {
            this.rbRotateLeft(parent);
            node = parent;
            parent = node.rbParent;
          }
          parent.rbRed = false;
          grandpa.rbRed = true;
          this.rbRotateRight(grandpa);
        }
      } else {
        uncle = grandpa.rbLeft;
        if (uncle && uncle.rbRed) {
          parent.rbRed = uncle.rbRed = false;
          grandpa.rbRed = true;
          node = grandpa;
        } else {
          if (node === parent.rbLeft) {
            this.rbRotateRight(parent);
            node = parent;
            parent = node.rbParent;
          }
          parent.rbRed = false;
          grandpa.rbRed = true;
          this.rbRotateLeft(grandpa);
        }
      }
      parent = node.rbParent;
    }
    this.beachline.root.rbRed = false;
  }

  /**
   * Remove a node from the RB-Tree
   */
  private rbRemoveNode(node: any): void {
    // >>> rhill 2011-05-27: Performance: cache previous/next nodes
    if (node.rbNext) {
      node.rbNext.rbPrevious = node.rbPrevious;
    }
    if (node.rbPrevious) {
      node.rbPrevious.rbNext = node.rbNext;
    }
    node.rbNext = node.rbPrevious = null;
    // <<<
    
    let parent = node.rbParent,
        left = node.rbLeft,
        right = node.rbRight,
        next;
        
    if (!left) {
      next = right;
    } else if (!right) {
      next = left;
    } else {
      next = this.getFirst(right);
    }
    
    if (parent) {
      if (parent.rbLeft === node) {
        parent.rbLeft = next;
      } else {
        parent.rbRight = next;
      }
    } else {
      this.beachline.root = next;
    }
    
    // enforce red-black rules
    let isRed;
    if (left && right) {
      isRed = next.rbRed;
      next.rbRed = node.rbRed;
      next.rbLeft = left;
      left.rbParent = next;
      if (next !== right) {
        parent = next.rbParent;
        next.rbParent = node.rbParent;
        node = next.rbRight;
        parent.rbLeft = node;
        next.rbRight = right;
        right.rbParent = next;
      } else {
        next.rbParent = parent;
        parent = next;
        node = next.rbRight;
      }
    } else {
      isRed = node.rbRed;
      node = next;
    }
    
    // 'node' is now the sole successor's child and 'parent' its
    // new parent (since the successor can have been moved)
    if (node) {
      node.rbParent = parent;
    }
    
    // the 'easy' cases
    if (isRed) { return; }
    if (node && node.rbRed) {
      node.rbRed = false;
      return;
    }
    
    // the other cases
    let sibling;
    do {
      if (node === this.beachline.root) {
        break;
      }
      if (node === parent.rbLeft) {
        sibling = parent.rbRight;
        if (sibling.rbRed) {
          sibling.rbRed = false;
          parent.rbRed = true;
          this.rbRotateLeft(parent);
          sibling = parent.rbRight;
        }
        if ((sibling.rbLeft && sibling.rbLeft.rbRed) || 
            (sibling.rbRight && sibling.rbRight.rbRed)) {
          if (!sibling.rbRight || !sibling.rbRight.rbRed) {
            sibling.rbLeft.rbRed = false;
            sibling.rbRed = true;
            this.rbRotateRight(sibling);
            sibling = parent.rbRight;
          }
          sibling.rbRed = parent.rbRed;
          parent.rbRed = sibling.rbRight.rbRed = false;
          this.rbRotateLeft(parent);
          node = this.beachline.root;
          break;
        }
      } else {
        sibling = parent.rbLeft;
        if (sibling.rbRed) {
          sibling.rbRed = false;
          parent.rbRed = true;
          this.rbRotateRight(parent);
          sibling = parent.rbLeft;
        }
        if ((sibling.rbLeft && sibling.rbLeft.rbRed) || 
            (sibling.rbRight && sibling.rbRight.rbRed)) {
          if (!sibling.rbLeft || !sibling.rbLeft.rbRed) {
            sibling.rbRight.rbRed = false;
            sibling.rbRed = true;
            this.rbRotateLeft(sibling);
            sibling = parent.rbLeft;
          }
          sibling.rbRed = parent.rbRed;
          parent.rbRed = sibling.rbLeft.rbRed = false;
          this.rbRotateRight(parent);
          node = this.beachline.root;
          break;
        }
      }
      sibling.rbRed = true;
      node = parent;
      parent = parent.rbParent;
    } while (!node.rbRed);
    
    if (node) { 
      node.rbRed = false; 
    }
  }

  /**
   * Rotate the tree to the left around the given node
   */
  private rbRotateLeft(node: any): void {
    let p = node,
          q = node.rbRight; // can't be null
    let parent = p.rbParent;
    
    if (parent) {
      if (parent.rbLeft === p) {
        parent.rbLeft = q;
      } else {
        parent.rbRight = q;
      }
    } else {
      this.beachline.root = q;
    }
    
    q.rbParent = parent;
    p.rbParent = q;
    p.rbRight = q.rbLeft;
    
    if (p.rbRight) {
      p.rbRight.rbParent = p;
    }
    
    q.rbLeft = p;
  }

  /**
   * Rotate the tree to the right around the given node
   */
  private rbRotateRight(node: any): void {
    let p = node,
          q = node.rbLeft; // can't be null
    let parent = p.rbParent;
    
    if (parent) {
      if (parent.rbLeft === p) {
        parent.rbLeft = q;
      } else {
        parent.rbRight = q;
      }
    } else {
      this.beachline.root = q;
    }
    
    q.rbParent = parent;
    p.rbParent = q;
    p.rbLeft = q.rbRight;
    
    if (p.rbLeft) {
      p.rbLeft.rbParent = p;
    }
    
    q.rbRight = p;
  }

  /**
   * Get the first node in the tree (leftmost)
   */
  private getFirst(node: any): any {
    while (node.rbLeft) {
      node = node.rbLeft;
    }
    return node;
  }

  /**
   * Get the last node in the tree (rightmost)
   */
  private getLast(node: any): any {
    while (node.rbRight) {
      node = node.rbRight;
    }
    return node;
  }

  /**
   * Diagram class for storing the result of the Voronoi algorithm
   */
  Diagram = function(this: any, site: any) {
    this.site = site;
  };

  /**
   * Cell class for representing a cell in the Voronoi diagram
   */
  Cell = function(this: any, site: any) {
    this.site = site;
    this.halfedges = [];
    this.closeMe = false;
  };

  /**
   * Initialize a cell with a site
   */
  initCell(cell: any, site: any): any {
    cell.site = site;
    cell.halfedges = [];
    cell.closeMe = false;
    return cell;
  }

  /**
   * Create a new cell for a site
   */
  createCell(site: any): any {
    let cell = this.cellJunkyard.pop();
    if (cell) {
      return this.initCell(cell, site);
    }
    return new this.Cell(site);
  }

  /**
   * Prepare the halfedges of a cell
   */
  prepareHalfedges(cell: any): number {
    let halfedges = cell.halfedges;
    let iHalfedge = halfedges.length;
    let edge;
    
    // get rid of unused halfedges
    while (iHalfedge--) {
      edge = halfedges[iHalfedge].edge;
      if (!edge.vb || !edge.va) {
        halfedges.splice(iHalfedge, 1);
      }
    }

    // sort them by angle
    halfedges.sort(function(a: any, b: any) { 
      return b.angle - a.angle; 
    });
    
    return halfedges.length;
  }

  /**
   * Get the neighbor IDs of a cell
   */
  getNeighborIds(cell: any): any[] {
    let neighbors: any[] = [];
    let iHalfedge = cell.halfedges.length;
    let edge;
    
    while (iHalfedge--) {
      edge = cell.halfedges[iHalfedge].edge;
      if (edge.lSite !== null && edge.lSite.voronoiId != cell.site.voronoiId) {
        neighbors.push(edge.lSite.voronoiId);
      } else if (edge.rSite !== null && edge.rSite.voronoiId != cell.site.voronoiId) {
        neighbors.push(edge.rSite.voronoiId);
      }
    }
    
    return neighbors;
  }

  /**
   * Get the bounding box of a cell
   */
  getBbox(cell: any): { x: number, y: number, width: number, height: number } {
    let halfedges = cell.halfedges;
    let iHalfedge = halfedges.length;
    let xmin = Infinity;
    let ymin = Infinity;
    let xmax = -Infinity;
    let ymax = -Infinity;
    let v, vx, vy;
    
    while (iHalfedge--) {
      v = halfedges[iHalfedge].getStartpoint();
      vx = v.x;
      vy = v.y;
      if (vx < xmin) { xmin = vx; }
      if (vy < ymin) { ymin = vy; }
      if (vx > xmax) { xmax = vx; }
      if (vy > ymax) { ymax = vy; }
    }
    
    return {
      x: xmin,
      y: ymin,
      width: xmax - xmin,
      height: ymax - ymin
    };
  }

  /**
   * Check if a point is inside, on, or outside a cell
   * @returns -1: outside, 0: on the perimeter, 1: inside
   */
  pointIntersection(cell: any, x: number, y: number): number {
    let halfedges = cell.halfedges;
    let iHalfedge = halfedges.length;
    let halfedge, p0, p1, r;
    
    while (iHalfedge--) {
      halfedge = halfedges[iHalfedge];
      p0 = halfedge.getStartpoint();
      p1 = halfedge.getEndpoint();
      r = (y - p0.y) * (p1.x - p0.x) - (x - p0.x) * (p1.y - p0.y);
      if (!r) {
        return 0;
      }
      if (r > 0) {
        return -1;
      }
    }
    
    return 1;
  }
  
  /**
   * Vertex class for representing a vertex in the Voronoi diagram
   */
  Vertex = function(this: any, x: number, y: number) {
    this.x = x;
    this.y = y;
  };

  /**
   * Edge class for representing an edge in the Voronoi diagram
   */
  Edge = function(this: any, lSite: any, rSite: any) {
    this.lSite = lSite;
    this.rSite = rSite;
    this.va = this.vb = null;
  };

  /**
   * Halfedge class for representing a halfedge in the Voronoi diagram
   */
  Halfedge = function(this: any, edge: any, lSite: any, rSite: any) {
    this.site = lSite;
    this.edge = edge;
    
    // 'angle' is a value to be used for properly sorting the
    // halfsegments counterclockwise. By convention, we will
    // use the angle of the line defined by the 'site to the left'
    // to the 'site to the right'.
    if (rSite) {
      this.angle = Math.atan2(rSite.y - lSite.y, rSite.x - lSite.x);
    } else {
      let va = edge.va,
            vb = edge.vb;
      
      // rhill 2011-05-31: used to call getStartpoint()/getEndpoint(),
      // but for performance purpose, these are expanded in place here.
      this.angle = edge.lSite === lSite ?
        Math.atan2(vb.x - va.x, va.y - vb.y) :
        Math.atan2(va.x - vb.x, vb.y - va.y);
    }
  };

  /**
   * Create a halfedge
   */
  createHalfedge(edge: any, lSite: any, rSite: any): any {
    return new this.Halfedge(edge, lSite, rSite);
  }

  /**
   * Get the start point of a halfedge
   */
  getStartpoint(halfedge: any): any {
    return halfedge.edge.lSite === halfedge.site ? halfedge.edge.va : halfedge.edge.vb;
  }

  /**
   * Get the end point of a halfedge
   */
  getEndpoint(halfedge: any): any {
    return halfedge.edge.lSite === halfedge.site ? halfedge.edge.vb : halfedge.edge.va;
  }

  /**
   * Create a vertex
   */
  createVertex(x: number, y: number): any {
    let v = this.vertexJunkyard.pop();
    if (!v) {
      v = new this.Vertex(x, y);
    } else {
      v.x = x;
      v.y = y;
    }
    this.vertices.push(v);
    return v;
  }

  /**
   * Create an edge
   */
  createEdge(lSite: any, rSite: any, va?: any, vb?: any): any {
    let edge = this.edgeJunkyard.pop();
    if (!edge) {
      edge = new this.Edge(lSite, rSite);
    } else {
      edge.lSite = lSite;
      edge.rSite = rSite;
      edge.va = edge.vb = null;
    }

    this.edges.push(edge);
    if (va) {
      this.setEdgeStartpoint(edge, lSite, rSite, va);
    }
    if (vb) {
      this.setEdgeEndpoint(edge, lSite, rSite, vb);
    }
    
    this.cells[lSite.voronoiId].halfedges.push(this.createHalfedge(edge, lSite, rSite));
    this.cells[rSite.voronoiId].halfedges.push(this.createHalfedge(edge, rSite, lSite));
    
    return edge;
  }

  /**
   * Create a border edge
   */
  createBorderEdge(lSite: any, va: any, vb: any): any {
    let edge = this.edgeJunkyard.pop();
    if (!edge) {
      edge = new this.Edge(lSite, null);
    } else {
      edge.lSite = lSite;
      edge.rSite = null;
    }
    
    edge.va = va;
    edge.vb = vb;
    this.edges.push(edge);
    
    return edge;
  }

  /**
   * Set the start point of an edge
   */
  setEdgeStartpoint(edge: any, lSite: any, rSite: any, vertex: any): void {
    if (!edge.va && !edge.vb) {
      edge.va = vertex;
      edge.lSite = lSite;
      edge.rSite = rSite;
    } else if (edge.lSite === rSite) {
      edge.vb = vertex;
    } else {
      edge.va = vertex;
    }
  }

  /**
   * Set the end point of an edge
   */
  setEdgeEndpoint(edge: any, lSite: any, rSite: any, vertex: any): void {
    this.setEdgeStartpoint(edge, rSite, lSite, vertex);
  }

  /**
   * Beachsection class
   */
  Beachsection = function(this: any) {
    // Constructor intentionally left empty
  };

  /**
   * Create a beachsection
   */
  createBeachsection(site: any): any {
    let beachsection = this.beachsectionJunkyard.pop();
    if (!beachsection) {
      beachsection = new this.Beachsection();
    }
    beachsection.site = site;
    return beachsection;
  }

  /**
   * Calculate the left breakpoint of a particular beach section
   */
  leftBreakPoint(arc: any, directrix: number): number {
    // http://en.wikipedia.org/wiki/Parabola
    // http://en.wikipedia.org/wiki/Quadratic_equation
    
    let site = arc.site;
    let rfocx = site.x;
    let rfocy = site.y;
    let pby2 = rfocy - directrix;
    
    // parabola in degenerate case where focus is on directrix
    if (!pby2) {
      return rfocx;
    }
    
    let lArc = arc.rbPrevious;
    if (!lArc) {
      return -Infinity;
    }
    
    let lfocx = lArc.site.x;
    let lfocy = lArc.site.y;
    let plby2 = lfocy - directrix;
    
    // parabola in degenerate case where focus is on directrix
    if (!plby2) {
      return lfocx;
    }
    
    let hl = lfocx - rfocx;
    let aby2 = 1 / pby2 - 1 / plby2;
    let b = hl / plby2;
    
    if (aby2) {
      return (-b + this.sqrt(b * b - 2 * aby2 * (hl * hl / (-2 * plby2) - lfocy + plby2 / 2 + rfocy - pby2 / 2))) / aby2 + rfocx;
    }
    
    // both parabolas have same distance to directrix, thus break point is midway
    return (rfocx + lfocx) / 2;
  }

  /**
   * Calculate the right breakpoint of a particular beach section
   */
  rightBreakPoint(arc: any, directrix: number): number {
    let rArc = arc.rbNext;
    if (rArc) {
      return this.leftBreakPoint(rArc, directrix);
    }
    
    let site = arc.site;
    return site.y === directrix ? site.x : Infinity;
  }

  /**
   * Detach a beachsection from the beachline
   */
  detachBeachsection(beachsection: any): void {
    this.detachCircleEvent(beachsection); // detach potentially attached circle event
    this.beachline.rbRemoveNode(beachsection); // remove from RB-tree
    this.beachsectionJunkyard.push(beachsection); // mark for reuse
  }

  /**
   * Detach a circle event from the beachsection
   */
  detachCircleEvent(beachsection: any): void {
    let circle = beachsection.circleEvent;
    if (circle) {
      if (!circle.rbPrevious) {
        this.firstCircleEvent = circle.rbNext;
      }
      this.circleEvents.rbRemoveNode(circle); // remove from RB-tree
      this.circleEventJunkyard.push(circle);
      beachsection.circleEvent = null;
    }
  }

  /**
   * Remove a beachsection from the beachline
   */
  removeBeachsection(beachsection: any): void {
    let circle = beachsection.circleEvent;
    let x = circle.x;
    let y = circle.ycenter;
    let vertex = this.createVertex(x, y);
    let previous = beachsection.rbPrevious;
    let next = beachsection.rbNext;
    let disappearingTransitions = [beachsection];
    
    // remove collapsed beachsection from beachline
    this.detachBeachsection(beachsection);

    // there could be more than one empty arc at the deletion point, this
    // happens when more than two edges are linked by the same vertex,
    // so we will collect all those edges by looking up both sides of
    // the deletion point.
    
    // look left
    let lArc = previous;
    while (lArc.circleEvent && 
           Math.abs(x - lArc.circleEvent.x) < 1e-9 && 
           Math.abs(y - lArc.circleEvent.ycenter) < 1e-9) {
      previous = lArc.rbPrevious;
      disappearingTransitions.unshift(lArc);
      this.detachBeachsection(lArc); // mark for reuse
      lArc = previous;
    }
    
    // even though it is not disappearing, I will also add the beach section
    // immediately to the left of the left-most collapsed beach section, for
    // convenience, since we need to refer to it later as this beach section
    // is the 'left' site of an edge for which a start point is set.
    disappearingTransitions.unshift(lArc);
    this.detachCircleEvent(lArc);

    // look right
    let rArc = next;
    while (rArc.circleEvent && 
           Math.abs(x - rArc.circleEvent.x) < 1e-9 && 
           Math.abs(y - rArc.circleEvent.ycenter) < 1e-9) {
      next = rArc.rbNext;
      disappearingTransitions.push(rArc);
      this.detachBeachsection(rArc); // mark for reuse
      rArc = next;
    }
    
    // we also have to add the beach section immediately to the right of the
    // right-most collapsed beach section, since there is also a disappearing
    // transition representing an edge's start point on its left.
    disappearingTransitions.push(rArc);
    this.detachCircleEvent(rArc);

    // walk through all the disappearing transitions between beach sections and
    // set the start point of their (implied) edge.
    let nArcs = disappearingTransitions.length;
    for (let iArc = 1; iArc < nArcs; iArc++) {
      rArc = disappearingTransitions[iArc];
      lArc = disappearingTransitions[iArc - 1];
      this.setEdgeStartpoint(rArc.edge, lArc.site, rArc.site, vertex);
    }

    // create a new edge as we have now a new transition between
    // two beach sections which were previously not adjacent.
    // since this edge appears as a new vertex is defined, the vertex
    // actually define an end point of the edge (relative to the site
    // on the left)
    lArc = disappearingTransitions[0];
    rArc = disappearingTransitions[nArcs - 1];
    rArc.edge = this.createEdge(lArc.site, rArc.site, undefined, vertex);

    // create circle events if any for beach sections left in the beachline
    // adjacent to collapsed sections
    this.attachCircleEvent(lArc);
    this.attachCircleEvent(rArc);
  }

  /**
   * Add a beachsection to the beachline
   */
  addBeachsection(site: any): void {
    let x = site.x;
    let directrix = site.y;

    // find the left and right beach sections which will surround the newly
    // created beach section.
    let lArc, rArc;
    let dxl, dxr;
    let node = this.beachline.root;

    while (node) {
      dxl = this.leftBreakPoint(node, directrix) - x;
      // x lessThanWithEpsilon xl => falls somewhere before the left edge of the beachsection
      if (dxl > 1e-9) {
        node = node.rbLeft;
      } else {
        dxr = x - this.rightBreakPoint(node, directrix);
        // x greaterThanWithEpsilon xr => falls somewhere after the right edge of the beachsection
        if (dxr > 1e-9) {
          if (!node.rbRight) {
            lArc = node;
            break;
          }
          node = node.rbRight;
        } else {
          // x equalWithEpsilon xl => falls exactly on the left edge of the beachsection
          if (dxl > -1e-9) {
            lArc = node.rbPrevious;
            rArc = node;
          }
          // x equalWithEpsilon xr => falls exactly on the right edge of the beachsection
          else if (dxr > -1e-9) {
            lArc = node;
            rArc = node.rbNext;
          }
          // falls exactly somewhere in the middle of the beachsection
          else {
            lArc = rArc = node;
          }
          break;
        }
      }
    }

    // create a new beach section object for the site and add it to RB-tree
    let newArc = this.createBeachsection(site);
    this.beachline.rbInsertSuccessor(lArc, newArc);

    // [null,null]
    // least likely case: new beach section is the first beach section on the
    // beachline.
    if (!lArc && !rArc) {
      return;
    }

    // [lArc,rArc] where lArc == rArc
    // most likely case: new beach section split an existing beach
    // section.
    if (lArc === rArc) {
      // invalidate circle event of split beach section
      this.detachCircleEvent(lArc);

      // split the beach section into two separate beach sections
      rArc = this.createBeachsection(lArc.site);
      this.beachline.rbInsertSuccessor(newArc, rArc);

      // since we have a new transition between two beach sections,
      // a new edge is born
      newArc.edge = rArc.edge = this.createEdge(lArc.site, newArc.site);

      // check whether the left and right beach sections are collapsing
      // and if so create circle events, to be notified when the point of
      // collapse is reached.
      this.attachCircleEvent(lArc);
      this.attachCircleEvent(rArc);
      return;
    }

    // [lArc,null]
    // even less likely case: new beach section is the *last* beach section
    // on the beachline -- this can happen *only* if *all* the previous beach
    // sections currently on the beachline share the same y value as
    // the new beach section.
    if (lArc && !rArc) {
      newArc.edge = this.createEdge(lArc.site, newArc.site);
      return;
    }

    // [null,rArc]
    // impossible case: because sites are strictly processed from top to bottom,
    // and left to right, which guarantees that there will always be a beach section
    // on the left -- except of course when there are no beach section at all on
    // the beach line, which case was handled above.

    // [lArc,rArc] where lArc != rArc
    // somewhat less likely case: new beach section falls *exactly* in between two
    // existing beach sections
    if (lArc !== rArc) {
      // invalidate circle events of left and right sites
      this.detachCircleEvent(lArc);
      this.detachCircleEvent(rArc);

      // an existing transition disappears, meaning a vertex is defined at
      // the disappearance point.
      // since the disappearance is caused by the new beachsection, the
      // vertex is at the center of the circumscribed circle of the left,
      // new and right beachsections.
      let lSite = lArc.site;
      let ax = lSite.x;
      let ay = lSite.y;
      let bx = site.x - ax;
      let by = site.y - ay;
      let rSite = rArc.site;
      let cx = rSite.x - ax;
      let cy = rSite.y - ay;
      let d = 2 * (bx * cy - by * cx);
      let hb = bx * bx + by * by;
      let hc = cx * cx + cy * cy;
      let vertex = this.createVertex(
        (cy * hb - by * hc) / d + ax, 
        (bx * hc - cx * hb) / d + ay
      );

      // one transition disappear
      this.setEdgeStartpoint(rArc.edge, lSite, rSite, vertex);

      // two new transitions appear at the new vertex location
      newArc.edge = this.createEdge(lSite, site, undefined, vertex);
      rArc.edge = this.createEdge(site, rSite, undefined, vertex);

      // check whether the left and right beach sections are collapsing
      // and if so create circle events, to handle the point of collapse.
      this.attachCircleEvent(lArc);
      this.attachCircleEvent(rArc);
      return;
    }
  }

  /**
   * CircleEvent class
   */
  CircleEvent = function(this: any) {
    this.arc = null;
    this.rbLeft = null;
    this.rbNext = null;
    this.rbParent = null;
    this.rbPrevious = null;
    this.rbRed = false;
    this.rbRight = null;
    this.site = null;
    this.x = this.y = this.ycenter = 0;
  };

  /**
   * Attach a circle event to a beach section
   */
  attachCircleEvent(arc: any): void {
    let lArc = arc.rbPrevious;
    let rArc = arc.rbNext;
    if (!lArc || !rArc) { return; } // does that ever happen?
    
    let lSite = lArc.site;
    let cSite = arc.site;
    let rSite = rArc.site;

    // If site of left beachsection is same as site of
    // right beachsection, there can't be convergence
    if (lSite === rSite) { return; }

    // Find the circumscribed circle for the three sites associated
    // with the beachsection triplet.
    let bx = cSite.x;
    let by = cSite.y;
    let ax = lSite.x - bx;
    let ay = lSite.y - by;
    let cx = rSite.x - bx;
    let cy = rSite.y - by;

    // If points l->c->r are clockwise, then center beach section does not
    // collapse, hence it can't end up as a vertex (we reuse 'd' here, which
    // sign is reverse of the orientation, hence we reverse the test.
    let d = 2 * (ax * cy - ay * cx);
    if (d >= -2e-12) { return; }

    let ha = ax * ax + ay * ay;
    let hc = cx * cx + cy * cy;
    let x = (cy * ha - ay * hc) / d;
    let y = (ax * hc - cx * ha) / d;
    let ycenter = y + by;

    // Important: ybottom should always be under or at sweep, so no need
    // to waste CPU cycles by checking

    // recycle circle event object if possible
    let circleEvent = this.circleEventJunkyard.pop();
    if (!circleEvent) {
      circleEvent = new this.CircleEvent();
    }
    
    circleEvent.arc = arc;
    circleEvent.site = cSite;
    circleEvent.x = x + bx;
    circleEvent.y = ycenter + this.sqrt(x * x + y * y); // y bottom
    circleEvent.ycenter = ycenter;
    arc.circleEvent = circleEvent;

    // find insertion point in RB-tree: circle events are ordered from
    // smallest to largest
    let predecessor = null;
    let node = this.circleEvents.root;
    
    while (node) {
      if (circleEvent.y < node.y || (circleEvent.y === node.y && circleEvent.x <= node.x)) {
        if (node.rbLeft) {
          node = node.rbLeft;
        } else {
          predecessor = node.rbPrevious;
          break;
        }
      } else {
        if (node.rbRight) {
          node = node.rbRight;
        } else {
          predecessor = node;
          break;
        }
      }
    }
    
    this.circleEvents.rbInsertSuccessor(predecessor, circleEvent);
    if (!predecessor) {
      this.firstCircleEvent = circleEvent;
    }
  }

  /**
   * Connect an edge to the bounding box
   */
  connectEdge(edge: any, bbox: BBox): boolean {
    // skip if end point already connected
    let vb = edge.vb;
    if (vb) { return true; }

    // make local copy for performance purpose
    let va = edge.va;
    let xl = bbox.xl;
    let xr = bbox.xr;
    let yt = bbox.yt;
    let yb = bbox.yb;
    let lSite = edge.lSite;
    let rSite = edge.rSite;
    let lx = lSite.x;
    let ly = lSite.y;
    let rx = rSite.x;
    let ry = rSite.y;
    let fx = (lx + rx) / 2;
    let fy = (ly + ry) / 2;
    let fm, fb;

    // if we reach here, this means cells which use this edge will need
    // to be closed, whether because the edge was removed, or because it
    // was connected to the bounding box.
    this.cells[lSite.voronoiId].closeMe = true;
    this.cells[rSite.voronoiId].closeMe = true;

    // get the line equation of the bisector if line is not vertical
    if (ry !== ly) {
      fm = (lx - rx) / (ry - ly);
      fb = fy - fm * fx;
    }

    // depending on the direction, find the best side of the
    // bounding box to use to determine a reasonable start point

    // special case: vertical line
    if (fm === undefined) {
      // doesn't intersect with viewport
      if (fx < xl || fx >= xr) { return false; }
      // downward
      if (lx > rx) {
        if (!va || va.y < yt) {
          va = this.createVertex(fx, yt);
        } else if (va.y >= yb) {
          return false;
        }
        vb = this.createVertex(fx, yb);
      }
      // upward
      else {
        if (!va || va.y > yb) {
          va = this.createVertex(fx, yb);
        } else if (va.y < yt) {
          return false;
        }
        vb = this.createVertex(fx, yt);
      }
    }
    // closer to vertical than horizontal, connect start point to the
    // top or bottom side of the bounding box
    else if (fm < -1 || fm > 1) {
      // downward
      if (lx > rx) {
        if (!va || va.y < yt) {
          va = this.createVertex((yt - fb) / fm, yt);
        } else if (va.y >= yb) {
          return false;
        }
        vb = this.createVertex((yb - fb) / fm, yb);
      }
      // upward
      else {
        if (!va || va.y > yb) {
          va = this.createVertex((yb - fb) / fm, yb);
        } else if (va.y < yt) {
          return false;
        }
        vb = this.createVertex((yt - fb) / fm, yt);
      }
    }
    // closer to horizontal than vertical, connect start point to the
    // left or right side of the bounding box
    else {
      // rightward
      if (ly < ry) {
        if (!va || va.x < xl) {
          va = this.createVertex(xl, fm * xl + fb);
        } else if (va.x >= xr) {
          return false;
        }
        vb = this.createVertex(xr, fm * xr + fb);
      }
      // leftward
      else {
        if (!va || va.x > xr) {
          va = this.createVertex(xr, fm * xr + fb);
        } else if (va.x < xl) {
          return false;
        }
        vb = this.createVertex(xl, fm * xl + fb);
      }
    }
    
    edge.va = va;
    edge.vb = vb;

    return true;
  }

  /**
   * Clip an edge using the Liang-Barsky algorithm
   */
  clipEdge(edge: any, bbox: BBox): boolean {
    let ax = edge.va.x;
    let ay = edge.va.y;
    let bx = edge.vb.x;
    let by = edge.vb.y;
    let t0 = 0;
    let t1 = 1;
    let dx = bx - ax;
    let dy = by - ay;
    
    // left
    let q = ax - bbox.xl;
    if (dx === 0 && q < 0) { return false; }
    let r = -q / dx;
    if (dx < 0) {
      if (r < t0) { return false; }
      if (r < t1) { t1 = r; }
    } else if (dx > 0) {
      if (r > t1) { return false; }
      if (r > t0) { t0 = r; }
    }
    
    // right
    q = bbox.xr - ax;
    if (dx === 0 && q < 0) { return false; }
    r = q / dx;
    if (dx < 0) {
      if (r > t1) { return false; }
      if (r > t0) { t0 = r; }
    } else if (dx > 0) {
      if (r < t0) { return false; }
      if (r < t1) { t1 = r; }
    }
    
    // top
    q = ay - bbox.yt;
    if (dy === 0 && q < 0) { return false; }
    r = -q / dy;
    if (dy < 0) {
      if (r < t0) { return false; }
      if (r < t1) { t1 = r; }
    } else if (dy > 0) {
      if (r > t1) { return false; }
      if (r > t0) { t0 = r; }
    }
    
    // bottom
    q = bbox.yb - ay;
    if (dy === 0 && q < 0) { return false; }
    r = q / dy;
    if (dy < 0) {
      if (r > t1) { return false; }
      if (r > t0) { t0 = r; }
    } else if (dy > 0) {
      if (r < t0) { return false; }
      if (r < t1) { t1 = r; }
    }

    // if we reach this point, Voronoi edge is within bbox

    // if t0 > 0, va needs to change
    // rhill 2011-06-03: we need to create a new vertex rather
    // than modifying the existing one, since the existing
    // one is likely shared with at least another edge
    if (t0 > 0) {
      edge.va = this.createVertex(ax + t0 * dx, ay + t0 * dy);
    }

    // if t1 < 1, vb needs to change
    // rhill 2011-06-03: we need to create a new vertex rather
    // than modifying the existing one, since the existing
    // one is likely shared with at least another edge
    if (t1 < 1) {
      edge.vb = this.createVertex(ax + t1 * dx, ay + t1 * dy);
    }

    // va and/or vb were clipped, thus we will need to close
    // cells which use this edge.
    if (t0 > 0 || t1 < 1) {
      this.cells[edge.lSite.voronoiId].closeMe = true;
      this.cells[edge.rSite.voronoiId].closeMe = true;
    }

    return true;
  }

  /**
   * Connect/cut edges at bounding box
   */
  clipEdges(bbox: BBox): void {
    // connect all dangling edges to bounding box
    // or get rid of them if it can't be done
    let edges = this.edges;
    let iEdge = edges.length;
    let edge;

    // iterate backward so we can splice safely
    while (iEdge--) {
      edge = edges[iEdge];
      // edge is removed if:
      //   it is wholly outside the bounding box
      //   it is looking more like a point than a line
      if (!this.connectEdge(edge, bbox) ||
          !this.clipEdge(edge, bbox) ||
          (Math.abs(edge.va.x - edge.vb.x) < 1e-9 && Math.abs(edge.va.y - edge.vb.y) < 1e-9)) {
        edge.va = edge.vb = null;
        edges.splice(iEdge, 1);
      }
    }
  }

  /**
   * Close the cells
   */
  closeCells(bbox: BBox): void {
    let xl = bbox.xl;
    let xr = bbox.xr;
    let yt = bbox.yt;
    let yb = bbox.yb;
    let cells = this.cells;
    let iCell = cells.length;
    let cell;
    let iLeft;
    let halfedges, nHalfedges;
    let edge;
    let va, vb, vz;
    let lastBorderSegment;

    while (iCell--) {
      cell = cells[iCell];
      // prune, order halfedges counterclockwise, then add missing ones
      // required to close cells
      if (!cell.prepareHalfedges()) {
        continue;
      }
      if (!cell.closeMe) {
        continue;
      }
      
      // find first 'unclosed' point.
      // an 'unclosed' point will be the end point of a halfedge which
      // does not match the start point of the following halfedge
      halfedges = cell.halfedges;
      nHalfedges = halfedges.length;
      
      // special case: only one site, in which case, the viewport is the cell
      // ...

      // all other cases
      iLeft = 0;
      while (iLeft < nHalfedges) {
        va = halfedges[iLeft].getEndpoint();
        vz = halfedges[(iLeft + 1) % nHalfedges].getStartpoint();
        // if end point is not equal to start point, we need to add the missing
        // halfedge(s) up to vz
        if (Math.abs(va.x - vz.x) >= 1e-9 || Math.abs(va.y - vz.y) >= 1e-9) {
          // find entry point:
          switch (true) {
            // walk downward along left side
            case this.equalWithEpsilon(va.x, xl) && this.lessThanWithEpsilon(va.y, yb):
              lastBorderSegment = this.equalWithEpsilon(vz.x, xl);
              vb = this.createVertex(xl, lastBorderSegment ? vz.y : yb);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
            // fall through

            // walk rightward along bottom side
            case this.equalWithEpsilon(va.y, yb) && this.lessThanWithEpsilon(va.x, xr):
              lastBorderSegment = this.equalWithEpsilon(vz.y, yb);
              vb = this.createVertex(lastBorderSegment ? vz.x : xr, yb);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
            // fall through

            // walk upward along right side
            case this.equalWithEpsilon(va.x, xr) && this.greaterThanWithEpsilon(va.y, yt):
              lastBorderSegment = this.equalWithEpsilon(vz.x, xr);
              vb = this.createVertex(xr, lastBorderSegment ? vz.y : yt);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
            // fall through

            // walk leftward along top side
            case this.equalWithEpsilon(va.y, yt) && this.greaterThanWithEpsilon(va.x, xl):
              lastBorderSegment = this.equalWithEpsilon(vz.y, yt);
              vb = this.createVertex(lastBorderSegment ? vz.x : xl, yt);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
              
              // walk downward along left side
              lastBorderSegment = this.equalWithEpsilon(vz.x, xl);
              vb = this.createVertex(xl, lastBorderSegment ? vz.y : yb);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
              
              // walk rightward along bottom side
              lastBorderSegment = this.equalWithEpsilon(vz.y, yb);
              vb = this.createVertex(lastBorderSegment ? vz.x : xr, yb);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
              va = vb;
              
              // walk upward along right side
              lastBorderSegment = this.equalWithEpsilon(vz.x, xr);
              vb = this.createVertex(xr, lastBorderSegment ? vz.y : yt);
              edge = this.createBorderEdge(cell.site, va, vb);
              iLeft++;
              halfedges.splice(iLeft, 0, this.createHalfedge(edge, cell.site, null));
              nHalfedges++;
              if (lastBorderSegment) { break; }
            // fall through

            default:
              throw "Voronoi.closeCells() > this makes no sense!";
          }
        }
        iLeft++;
      }
      cell.closeMe = false;
    }
  }

  /**
   * Quantize sites to improve robustness
   */
  quantizeSites(sites: Site[]): void {
    let ε = this.ε;
    let n = sites.length;
    let site;
    
    while (n--) {
      site = sites[n];
      site.x = Math.floor(site.x / ε) * ε;
      site.y = Math.floor(site.y / ε) * ε;
    }
  }

  /**
   * Recycle a diagram
   */
  recycle(diagram: any): void {
    if (diagram) {
      if (diagram instanceof this.Diagram) {
        this.toRecycle = diagram;
      } else {
        throw 'Voronoi.recycleDiagram() > Need a Diagram object.';
      }
    }
  }

  /**
   * Compute the Voronoi diagram
   */
  compute(sites: Site[], bbox: BBox): VDiagram {
    // to measure execution time
    let startTime = new Date();

    // init internal state
    this.reset();

    // any diagram data available for recycling?
    // I do that here so that this is included in execution time
    if (this.toRecycle) {
      this.vertexJunkyard = this.vertexJunkyard.concat(this.toRecycle.vertices);
      this.edgeJunkyard = this.edgeJunkyard.concat(this.toRecycle.edges);
      this.cellJunkyard = this.cellJunkyard.concat(this.toRecycle.cells);
      this.toRecycle = null;
    }

    // Initialize site event queue
    let siteEvents = sites.slice(0);
    siteEvents.sort((a, b) => {
      let r = b.y - a.y;
      if (r) { return r; }
      return b.x - a.x;
    });

    // process queue
    let site = siteEvents.pop();
    let siteid = 0;
    let xsitex: number, xsitey: number; // to avoid duplicate sites
    let cells = this.cells;
    let circle;

    // main loop
    for (;;) {
      // we need to figure whether we handle a site or circle event
      // for this we find out if there is a site event and it is
      // 'earlier' than the circle event
      circle = this.firstCircleEvent;

      // add beach section
      if (site && (!circle || site.y < circle.y || (site.y === circle.y && site.x < circle.x))) {
        // only if site is not a duplicate
        if (site.x !== xsitex || site.y !== xsitey) {
          // first create cell for new site
          cells[siteid] = this.createCell(site);
          site.voronoiId = siteid++;
          // then create a beachsection for that site
          this.addBeachsection(site);
          // remember last site coords to detect duplicate
          xsitey = site.y;
          xsitex = site.x;
        }
        site = siteEvents.pop();
      }
      // remove beach section
      else if (circle) {
        this.removeBeachsection(circle.arc);
      }
      // all done, quit
      else {
        break;
      }
    }

    // wrapping-up:
    //   connect dangling edges to bounding box
    //   cut edges as per bounding box
    //   discard edges completely outside bounding box
    //   discard edges which are point-like
    this.clipEdges(bbox);

    //   add missing edges in order to close opened cells
    this.closeCells(bbox);

    // to measure execution time
    let stopTime = new Date();

    // prepare return values
    let diagram = new this.Diagram();
    diagram.cells = this.cells;
    diagram.edges = this.edges;
    diagram.vertices = this.vertices;
    diagram.execTime = stopTime.getTime() - startTime.getTime();

    // clean up
    this.reset();

    return diagram;
  }
}

/**
 * Get polygons from a Voronoi diagram
 */
function getVoronoiPolygons(diagram: VDiagram, origSiteList?: VSite[]): { x: number, y: number }[][] {
  let idSortedCells = origSiteList?.map(s => diagram.cells[s.voronoiId]) ?? diagram.cells;
  return idSortedCells.map(cell => {
    return cell.halfedges.map(halfedge => {
      return halfedge.getStartpoint();
    });
  });
}

/**
 * Filter points that are too close to each other in a polygon
 */
function filterSimilarPoints(points: { x: number, y: number }[], threshold: number = 0.002): { x: number, y: number }[] {
  let indexesTooCloseToPrevious = new Set<number>();
  
  for (let i = 0; i < points.length - 1; i++) {
    let pt = points[i];
    let nextPt = points[i + 1];
    if (Math.abs(pt.x - nextPt.x) < threshold && Math.abs(pt.y - nextPt.y) < threshold) {
      indexesTooCloseToPrevious.add(i + 1);
    }
  }

  let pt = points[0];
  let nextPt = points[points.length - 1];
  if (Math.abs(pt.x - nextPt.x) < threshold && Math.abs(pt.y - nextPt.y) < threshold) {
    indexesTooCloseToPrevious.add(points.length - 1);
  }

  let filteredPts = points.filter((pt, i) => !indexesTooCloseToPrevious.has(i));

  // Check first and last point - if too close, remove last point
  let pt2 = filteredPts[0];
  let nextPt2 = filteredPts[filteredPts.length - 1];
  if (Math.abs(pt2.x - nextPt2.x) < threshold && Math.abs(pt2.y - nextPt2.y) < threshold) {
    filteredPts.pop();
  }

  return filteredPts;
}

export {
  Voronoi,
  getVoronoiPolygons,
  filterSimilarPoints
};