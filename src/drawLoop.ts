import { appState } from "./appState";
import type p5 from "p5";
import { Voronoi, filterSimilarPoints, getVoronoiPolygons } from "./voronoi";
import { getVoronoiData } from "./tdWebsockets";

const lerp = (a: number, b: number, t: number) => {
  return a + (b - a) * t;
};

const voronoi = new Voronoi();
const initialPts = [
  { x: 300, y: 300 },
  { x: 600, y: 600 },
];
const p5bbox = { xl: 0, xr: 1280, yt: 0, yb: 720 };
//todo don't need normalizing - bug fixed with noise preventing sites in perfect circles
const normBbox = { xl: 0, xr: 1, yt: 0, yb: 1 };
const normInitialPts = initialPts.map((pt) => ({
  x: pt.x / p5bbox.xr,
  y: pt.y / p5bbox.yb,
}));
let diagram = voronoi.compute(normInitialPts, normBbox);

let lastPolygons: { x: number; y: number }[][] = [];
let lastColors: { r: number; g: number; b: number }[] = [];

let centroidMap = new Map<number, { x: number; y: number }>();
let numPtsMap = new Map<number, number[]>();
Array.from(Array(20).keys()).forEach((i) => {
  centroidMap.set(i, { x: 0, y: 0 });
  numPtsMap.set(i, []);
});

appState.drawFunctions.push((p: p5) => {
  
  try {
    appState.voronoiSites.splice(0, appState.voronoiSites.length);

    const tdVoronoiData = getVoronoiData();

    //whether to add noise to fix parallel line crashes.
    //noise affects stability of filtered centroid calculations
    const addNoise = false;

    const tdSites = tdVoronoiData.x.map((x, i) => ({
      x,
      y: tdVoronoiData.y[i] + (addNoise ? Math.random() * 0.00001 : 0),
    }));
    const tdColors = tdVoronoiData.r.map((r, i) => ({
      r: r * 255,
      g: tdVoronoiData.g[i] * 255,
      b: tdVoronoiData.b[i] * 255,
    }));

    const sites = tdSites;
    const cols = tdColors;
    if (sites.length != lastPolygons.length) {
      console.log("sites length changed", sites.length, lastPolygons.length);
    }
    if (sites.length != cols.length) {
      console.log("site col mismatch", sites.length, cols.length);
    }

    try {
      if (diagram) voronoi.recycle(diagram);
      diagram = voronoi.compute(sites, normBbox);
      //todo api - indicate that compute mutates the input array to have voronoiId
      //@ts-ignore
      lastPolygons = getVoronoiPolygons(diagram, sites);
      lastColors = cols;
    } catch (e) {
      console.warn("voronoi compute failed", e);
      diagram = null;
    }

    if (
      sites.length != lastPolygons.length ||
      sites.length != lastColors.length
    ) {
      console.log(
        "sites length changed - STILL OFF",
        sites.length,
        lastPolygons.length,
        lastColors.length
      );
    }

    if (true) {
      p.push();
      const strokeColor = {
        r: tdVoronoiData.borderR * 255,
        g: tdVoronoiData.borderG * 255,
        b: tdVoronoiData.borderB * 255,
      };
      p.stroke(strokeColor.r, strokeColor.g, strokeColor.b);
      p.strokeWeight(tdVoronoiData.lineThickness);
      lastPolygons.forEach((polygon, i) => {
        const color = lastColors[i];
        if (tdVoronoiData.edgeUsesPalleteCols) {
          p.stroke(color.r, color.g, color.b);
        }
        if (tdVoronoiData.edgeOnly) {
          p.noFill();
        } else {
          p.fill(color.r, color.g, color.b);
        }

        p.beginShape();
        let centroid = { x: 0, y: 0 };
        const filteredPolygon = filterSimilarPoints(polygon, 0.02);
        const poly = filteredPolygon;
        poly.forEach((pt) => {
          centroid.x += pt.x;
          centroid.y += pt.y;
        });
        centroid.x /= poly.length;
        centroid.y /= poly.length;

        centroid.x = sites[i].x;
        centroid.y = sites[i].y;

        const centroidLerp = tdVoronoiData.centroidLerp;

        //todo - need to define numPtsMap with keys equal to actual num polysites
        // let numPtslist = numPtsMap.get(i)!
        // numPtslist.push(poly.length)
        // if (numPtslist.length > 3) numPtslist.shift()

        //if all 3 items in numPtsList are different, then we have a new centroid
        // if(numPtslist[0] !== numPtslist[1] && numPtslist[1] !== numPtslist[2]) {
        //   console.log("thrasing")
        // }

        // if (i == 0) {
        //   console.log("centroid", filteredPolygon.length - polygon.length)
        //   p.endShape(p.CLOSE)
        //   // return
        // }
        // if (filteredPolygon.length > 4) {
        //   const fp = filteredPolygon.map(v => ({x: v.x , y: v.y }))
        //   console.log("filteredPolygon", filteredPolygon.length, "polygon", polygon.length)
        // }

        polygon.forEach((pt) =>
          p.vertex(
            lerp(pt.x, centroid.x, centroidLerp) * p5bbox.xr,
            lerp(pt.y, centroid.y, centroidLerp) * p5bbox.yb
          )
        );
        p.endShape(p.CLOSE);
      });
      p.pop();
    } else {
      p.push();
      sites.forEach((site, i) => {
        const color = cols[i];
        p.fill(color.r, color.g, color.b);
        p.noStroke();
        p.circle(site.x * p5bbox.xr, site.y * p5bbox.yb, 10);
      });
      p.pop();
    }

    if (true) {
      p.push();
      sites.forEach((site) => {
        p.fill(255);
        p.circle(site.x * p5bbox.xr, site.y * p5bbox.yb, 10);
      });
      p.pop();
    }
  } catch (e) {
    console.warn("error in draw", e);
  }
});

// const passthru = new Passthru({ src: p5Canvas })
// const canvasPaint = new CanvasPaint({ src: passthru })

// shaderGraphEndNode = canvasPaint
// appState.shaderDrawFunc = () => shaderGraphEndNode!!.renderAll(appState.threeRenderer!!)
