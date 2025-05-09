import p5 from 'p5'



export type TemplateAppState = {
  p5Instance: p5 | undefined
  codeStack: (() => void)[]
  codeStackIndex: number
  drawFunctions: ((p5: p5) => void)[]
  oneTimeDrawFuncs: ((p5: p5) => void)[]
  drawFuncMap: Map<string, (p5: p5) => void>
  shaderDrawFunc: (() => void) | undefined
  stats?: { begin: () => void, end: () => void }
  paused: boolean
  drawing: boolean,
  voronoiSites: {x: number, y: number}[]
}

export const appState: TemplateAppState = {
  p5Instance: undefined,
  codeStack: [],
  codeStackIndex: 0,
  drawFunctions: [],
  oneTimeDrawFuncs: [],
  drawFuncMap: new Map<string, (p5: p5) => void>(),
  shaderDrawFunc: undefined,
  stats: undefined,
  paused: false,
  drawing: false,
  voronoiSites: []
} 

export const appStateName = 'voronoiTestAppState'

//todo api - add caching/rehydrating of appState from local storage

// export const globalStore = defineStore(appStateName, () => {
//   const appStateRef = ref(appState)

//   //@ts-ignore
//   window.appState = appStateRef

//   return { appStateRef }
// });

// if (import.meta.hot) {
//   import.meta.hot.accept(acceptHMRUpdate(globalStore, import.meta.hot))
// } 