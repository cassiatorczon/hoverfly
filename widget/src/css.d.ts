// Lets `tsc` understand `import styles from './foo.css'`. The actual loading of
// the file contents as a string happens in rollup (see the `css-as-string`
// plugin in rollup.config.js).
declare module '*.css' {
  const content: string
  export default content
}
