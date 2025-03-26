import './style.css'
import { createP5Sketch } from './createSketch'
import { appState } from './appState'

const p5Canvas = document.getElementById('p5Canvas') as HTMLCanvasElement
const p5i = createP5Sketch(p5Canvas, () => appState)

